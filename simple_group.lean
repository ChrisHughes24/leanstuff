import group_theory.perm group_theory.order_of_element data.set.finite

open equiv

example : (⟨1, rfl⟩ : {x : perm bool // x = 1}) = ⟨swap ff tt * swap ff tt, dec_trivial⟩ :=
subtype.eq dec_trivial

@[instance, priority 1000] def foo {α : Type*} [decidable_eq α] {P : α → Prop} :
  decidable_eq (subtype P) :=
λ a b, decidable_of_iff (a.1 = b.1) (by cases a; cases b; simp)

example : (⟨1, rfl⟩ : {x : perm bool // x = 1}) = ⟨swap ff tt * swap ff tt, dec_trivial⟩ :=
dec_trivial

universes u v
open finset is_subgroup equiv equiv.perm

class simple_group (G : Type u) [group G] : Prop :=
(simple : ∀ (H : set G) [normal_subgroup H], H = trivial G ∨ H = set.univ)


variables {G : Type u} [group G] [fintype G] [decidable_eq G]

-- lemma simple_group_def : simple_group G ↔
--   ∀ (H : set G) [normal_subgroup H], H = trivial G ∨ H = set.univ :=
-- ⟨@simple_group.simple _ _, simple_group.mk⟩

-- lemma simple_group_iff_finset : simple_group G ↔
--   ∀ (H : finset G) [normal_subgroup H], H = trivial G ∨ H = set.univ

def conjugacy_class (a : G) : finset G :=
(@univ G _).image (λ x, x * a * x⁻¹)

#eval conjugacy_class (-1 : units ℤ)
#print finset.erase
lemma mem_conjugacy_class {a b : G} : b ∈ conjugacy_class a ↔ is_conj a b := sorry

def conjugacy_classes : Π l : list G, finset (finset G)
| []     := ∅
| (a::l) :=
let x := (conjugacy_class a) in
have (l.filter (∉ x)).length < 1 + l.length,
  from lt_of_le_of_lt (list.length_le_of_sublist (list.filter_sublist _))
    (by rw add_comm; exact nat.lt_succ_self _),
insert x (conjugacy_classes (l.filter (∉ x)))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩]}

def conjugacy_classes' (G : Type u) [group G] [fintype G] [decidable_eq G] : finset (finset G) :=
quotient.lift_on (@univ G _).1 conjugacy_classes sorry


meta def thing {α : Type*} [has_reflect α] (f : α) : tactic unit :=
tactic.exact `(f)

def is_conjugacy_partition (s : finset (finset G)) : Prop :=
(∀ x, ∃ t ∈ s, x ∈ t) ∧ ∀ t ∈ s, ∃ x ∈ t, ∀ y, y ∈ t ↔ is_conj x y

instance {α β : Type*} [group α] [group β] [decidable_eq β] (f : α → β) [is_group_hom f] :
  decidable_pred (is_group_hom.ker f) :=
λ _, decidable_of_iff _ (is_group_hom.mem_ker f).symm

def alternating (α : Type*) [decidable_eq α] [fintype α] : Type* :=
is_group_hom.ker (sign : perm α → units ℤ)

instance (α : Type*) [decidable_eq α] [fintype α] : decidable_eq (alternating α) :=
λ a b, decidable_of_iff (a.1 = b.1) (by cases a; cases b; simp [subtype.mk.inj_eq])

#print alternating.decidable_eq
#print subtype.decidable_eq

instance (α : Type*) [decidable_eq α] [fintype α] : fintype (alternating α) :=
set_fintype _

noncomputable def quotient_ker_equiv_range {α β : Type*} [group α] [group β] (f : α → β) [is_group_hom f] :
  (quotient_group.quotient (is_group_hom.ker f)) ≃ set.range f :=
@equiv.of_bijective _ _ (λ x, quotient.lift_on' x (λ a, show set.range f, from ⟨f a, a, rfl⟩)
  (λ a b (h : @setoid.r _ (quotient_group.left_rel (is_group_hom.ker f)) a b),
    have h : a⁻¹ * b ∈ is_group_hom.ker f, from h,
    subtype.eq
    (by rw [is_group_hom.mem_ker, is_group_hom.mul f,
        is_group_hom.inv f, inv_mul_eq_iff_eq_mul, mul_one] at h;
      simp [h])))
  ⟨λ a b, quotient.induction_on₂' a b
      (λ a b h, quotient.sound' (show a⁻¹ * b ∈ is_group_hom.ker f,
        by rw [is_group_hom.mem_ker, is_group_hom.mul f, is_group_hom.inv f,
          show f a = f b, from subtype.mk.inj h]; simp)),
    λ ⟨b, a, hab⟩, ⟨quotient_group.mk a, subtype.eq hab⟩⟩

noncomputable def quotient_ker_equiv_of_surjective {α β : Type*} [group α] [group β]
  (f : α → β) [is_group_hom f] (hf : function.surjective f) :
  (quotient_group.quotient (is_group_hom.ker f)) ≃ β :=
calc (quotient_group.quotient (is_group_hom.ker f)) ≃ set.range f : quotient_ker_equiv_range _
... ≃ β : ⟨λ a, a.1, λ b, ⟨b, hf b⟩, λ ⟨_, _⟩, rfl, λ _, rfl⟩

section classical

local attribute [instance] classical.prop_decidable

lemma sign_surjective {α : Type*} [decidable_eq α] [fintype α] (hα : 1 < fintype.card α) :
  function.surjective (sign : perm α → units ℤ) :=
λ a, (int.units_eq_one_or a).elim
  (λ h, ⟨1, by simp [h]⟩)
  (λ h, let ⟨x⟩ := fintype.card_pos_iff.1 (lt_trans zero_lt_one hα) in
    let ⟨y, hxy⟩ := fintype.exists_ne_of_card_gt_one hα x in
    ⟨swap y x, by rw [sign_swap hxy, h]⟩ )

lemma card_alternating (α : Type*) [decidable_eq α] [fintype α] (h : 2 ≤ fintype.card α):
  fintype.card (alternating α) * 2 = (fintype.card α).fact :=
have (quotient_group.quotient (is_group_hom.ker (sign : perm α → units ℤ))) ≃ units ℤ,
  from quotient_ker_equiv_of_surjective _ (sign_surjective h),
calc fintype.card (alternating α) * 2 = fintype.card (units ℤ × alternating α) :
  by rw [mul_comm, fintype.card_prod, fintype.card_units_int]
... = fintype.card (perm α) : fintype.card_congr
  (calc (units ℤ × alternating α) ≃
    (quotient_group.quotient (is_group_hom.ker (sign : perm α → units ℤ)) × alternating α)  :
      equiv.prod_congr this.symm (by refl)
  ... ≃ perm α : (group_equiv_quotient_times_subgroup _).symm)
... = (fintype.card α).fact : fintype.card_perm

instance (α : Type*) [decidable_eq α] [fintype α] : group (alternating α) :=
by unfold alternating; apply_instance

end classical


local notation `A5` := alternating (fin 5)
variables {α : Type*} [fintype α] [decidable_eq α]

section
local attribute [semireducible] reflected

-- meta instance (n : ℕ) : has_reflect (fin n) :=
-- nat.cases_on n (λ a, fin.elim0 a) $
-- λ n a, show reflected a, from `(@has_coe.coe ℕ (fin (nat.succ %%`(n))) _
--   (%%(nat.reflect a.1)))

-- meta instance (n : ℕ) (e : expr): has_reflect (fin n) :=
-- λ a, `(@fin.mk %%e %%(nat.reflect a.1) (of_as_true %%`(_root_.trivial)))

meta instance fin_reflect (n : ℕ) : has_reflect (fin n) :=
λ a, `(@fin.mk %%`(n) %%(nat.reflect a.1) (of_as_true %%`(_root_.trivial)))

-- λ a, expr.app (expr.app (expr.const `fin.mk []) `(a.1))
--   `(of_as_true trivial)

--#print fin.has_reflect
-- meta instance (n : ℕ) : has_reflect (perm (fin n)) :=
-- list.rec_on (quot.unquot (@univ (fin n) _).1)
--   (λ f, `(1 : perm (fin n)))
--   (λ x l ih f, let e : expr := ih (swap x (f x) * f) in
--     if x = f x then e
--     else if e = `(1 : perm (fin %%`(n)))
--     then `(@swap (fin %%`(n)) _ (%%`(x)) (%%(@reflect (fin n)
--       (f x) (fin.has_reflect n (f x)))))
--     else `(@swap (fin %%`(n)) _ (%%`(x)) (%%(@reflect (fin n)
--       (f x) (fin.has_reflect n (f x)))) * %%e))

meta instance fin_fun.has_reflect : has_reflect (fin 5 → fin 5) :=
list.rec_on (quot.unquot (@univ (fin 5) _).1)
  (λ f, `(λ y : fin 5, y))
  (λ x l ih f, let e := ih f in
    if f x = x then e
    else let ex := fin_reflect 5 x in
      let efx := fin_reflect 5 (f x) in
      if e = `(λ y : fin 5, y)
      then `(λ y : fin 5, ite.{1} (y = %%ex) (%%efx) y)
      else `(λ y : fin 5, ite.{1} (y = %%ex) (%%efx) ((%%e : fin 5 → fin 5) y)))
#print equiv.mk

instance {α β : Type*} [fintype α] [decidable_eq α] (f : α → β) (g : β → α) :
  decidable (function.right_inverse f g) :=
show decidable (∀ x, g (f x) = x), by apply_instance

instance {α β : Type*} [fintype β] [decidable_eq β] (f : α → β) (g : β → α) :
  decidable (function.left_inverse f g) :=
show decidable (∀ x, f (g x) = x), by apply_instance

meta instance : has_reflect (perm (fin 5)) :=
λ f, `(@equiv.mk.{1 1} (fin 5) (fin 5)
    %%(fin_fun.has_reflect f.to_fun)
  %%(fin_fun.has_reflect f.inv_fun)
  (of_as_true %%`(_root_.trivial)) (of_as_true %%`(_root_.trivial)))

#print is_group_hom.mem_ker

meta instance I4 : has_reflect (alternating (fin 5)) :=
λ f, `(@subtype.mk (perm (fin 5)) (is_group_hom.ker (sign : perm (fin 5) → units ℤ))
   %%(@reflect (perm (fin 5)) f.1 (equiv.perm.has_reflect f.1))
  ((is_group_hom.mem_ker sign).2 %%`(@eq.refl (units ℤ) 1)))

meta def afsf : has_reflect (list (list (list ℕ))) := by apply_instance
-- set_option pp.all true

instance f {α : Type*} [decidable_eq α] : decidable_pred (multiset.nodup : multiset α → Prop) :=
by apply_instance

meta instance multiset.has_reflect {α : Type} [reflected α] [has_reflect α] :
  has_reflect (multiset α) :=
λ s, let l : list α := quot.unquot s in `(@quotient.mk.{1} (list %%`(α)) _ %%`(l))

meta instance I1 : has_reflect (finset (alternating (fin 5) × alternating (fin 5))) :=
λ s, `(let t : multiset (alternating (fin 5) × alternating (fin 5)) := %%(multiset.has_reflect s.1) in
    @finset.mk.{0} (alternating (fin 5) × alternating (fin 5)) t (of_as_true %%`(_root_.trivial)))
--#print prod.has_reflect
meta instance I3 (a : alternating (fin 5)) :
  has_reflect {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1} :=
λ b, `(@subtype.mk (alternating (fin 5) × alternating (fin 5))
  (λ b, b.2 * %%`(a) * b.2⁻¹ = b.1)
  %%(prod.has_reflect _ _ b.1) (of_as_true %%`(_root_.trivial)))

meta instance I5 (a : alternating (fin 5)) (m : reflected a) :
  reflected {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1} :=
`({b : alternating (fin 5) × alternating (fin 5) // b.2 * %%m * b.2⁻¹ = b.1})

meta instance test : has_reflect (Σ n : ℕ, {m // m = n}) :=
λ x, `(@sigma.mk ℕ (λ n : ℕ, {m // m = n}) %%(nat.reflect (x.1 : ℕ))
  (subtype.mk %%(nat.reflect x.2.1) %%`(@eq.refl ℕ %%(nat.reflect x.1))))

def n : (Σ n : ℕ, {m // m = n}) :=
by thing (show Σ n : ℕ, {m // m = n}, from ⟨5, ⟨5, rfl⟩⟩)

#print n

meta instance I2 : has_reflect
  (Σ a : alternating (fin 5), finset
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1}) :=
λ s, let ra : reflected s.1 := (I4 s.1) in
  `(let a : alternating (fin 5) := %%ra in
  let t : multiset {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1} :=
    %%(@multiset.has_reflect _ (I5 s.1 ra) (I3 s.1) s.2.1) in
  @sigma.mk (alternating (fin 5))
    (λ a, finset {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1})
    a (finset.mk t (of_as_true %%`(_root_.trivial))))

meta instance I6 : has_reflect (finset
  (Σ a : alternating (fin 5), finset
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1})) :=
λ s, `(@finset.mk  (Σ a : alternating (fin 5), finset
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1})
  %%(@multiset.has_reflect _ _ I2 s.1)
  (of_as_true %%`(_root_.trivial)))

meta instance I7 : has_reflect
  (Σ a : alternating (fin 5), multiset
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1}) :=
λ s, let ra : reflected s.1 := (I4 s.1) in
`(let a : alternating (fin 5) := %%ra in
  @sigma.mk (alternating (fin 5))
    (λ a, multiset {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1})
    a %%(@multiset.has_reflect _ (I5 s.1 ra) (I3 s.1) s.2))


-- meta instance finset_finset.has_reflect (n : ℕ) : has_reflect (finset (finset (alternating (fin n)))) :=
-- λ s, `(let m : ℕ := %%`(n) in
--   let t : multiset (finset (alternating (fin m))) := %%(multiset.has_reflect s.1) in
--   @finset.mk.{0} (finset (alternating (fin m))) t (of_as_true %%`(_root_.trivial)))

-- instance afhasf (n : ℕ) : decidable_eq (finset (alternating (fin n) × alternating (fin n)) × alternating (fin n)) :=
--  by apply_instance

-- meta instance hklkhfhndihn (n : ℕ) : has_reflect
--   (finset (finset (alternating (fin n) × alternating (fin n)) × alternating (fin n))) :=
-- λ s, `(let m : ℕ := %%`(n) in
--   let t : multiset (finset (alternating (fin m) × alternating (fin m)) × alternating (fin m)) :=
--       %%(multiset.has_reflect s.1) in
--     @finset.mk.{0} (finset (alternating (fin m) × alternating (fin m)) × alternating (fin m)) t
--       (of_as_true %%`(_root_.trivial)))

end
#print expr
meta instance : has_reflect (list (list (perm (fin 5)))) := by apply_instance



 meta def whatever {α : Sort*} : α := whatever

-- meta def conjugacy_classes_A5_aux : list (alternating (fin 5)) → list (list (alternating (fin 5) ×
--   alternating (fin 5)) × alternating (fin 5))
-- | [] := ∅
-- | (a :: l) :=
-- let m := (((quot.unquot (@univ (alternating (fin 5)) _).1).map
--   (λ x, (x * a * x⁻¹, x))).pw_filter (λ x y, x.1 ≠ y.1), a)
--   in m :: conjugacy_classes_A5_aux (l.diff (list.map prod.fst m.1))

-- meta def whatever {α : Sort*} : α := whatever

-- meta def conjugacy_classes_A5 : finset (finset (alternating (fin 5) ×
--   alternating (fin 5)) × alternating (fin 5)) :=
-- finset.mk (↑((conjugacy_classes_A5_aux (quot.unquot univ.1)).map
--   (λ l : list (alternating (fin 5) ×
--     alternating (fin 5)) × alternating (fin 5),
--     show  finset (alternating (fin 5) ×
--      alternating (fin 5)) × alternating (fin 5),
--       from (finset.mk (↑l.1 : multiset _) whatever, l.2))) : multiset _) whatever
-- set_option profiler true

meta def conjugacy_classes_A5_meta_aux : list (alternating (fin 5)) → list
  (Σ a : alternating (fin 5), list
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1})
| [] := []
| (a :: l) := let m : Σ a : alternating (fin 5), list
    {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1} :=
  ⟨a, ((quot.unquot (@univ (alternating (fin 5)) _).1).map
  (λ x, show {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1},
    from ⟨(x * a * x⁻¹, x), rfl⟩)).pw_filter (λ x y, x.1.1 ≠ y.1.1)⟩ in
m :: conjugacy_classes_A5_meta_aux (l.diff (m.2.map (prod.fst ∘ subtype.val)))

meta def conjugacy_classes_A5_meta : multiset (Σ a : alternating (fin 5), multiset
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1}) :=
(quotient.mk ((conjugacy_classes_A5_meta_aux (quot.unquot univ.1)).map
    (λ a, ⟨a.1, (quotient.mk a.2)⟩)))

@[irreducible] def conjugacy_classes_A5_aux : multiset (Σ a : alternating (fin 5), multiset
  {b : alternating (fin 5) × alternating (fin 5) // b.2 * a * b.2⁻¹ = b.1}) :=
by thing (conjugacy_classes_A5_meta)
#print conjugacy_classes_A5_aux
def conjugacy_classes_A5_aux2 : multiset (multiset (alternating (fin 5))) :=
conjugacy_classes_A5_aux.map (λ s, s.2.map (λ b, b.1.1))

lemma nodup_conjugacy_classes_A5_aux2 : ∀ s : multiset (alternating (fin 5)),
  s ∈ conjugacy_classes_A5_aux2 → s.nodup :=
dec_trivial

def conjugacy_classes_A5 : finset (finset (alternating (fin 5))) :=
⟨conjugacy_classes_A5_aux2.pmap finset.mk nodup_conjugacy_classes_A5_aux2, dec_trivial⟩

lemma is_conj_conjugacy_classes_A5 (s : finset A5) (h : s ∈ conjugacy_classes_A5) :
  ∀ x y ∈ s, is_conj x y :=
assume x y hx hy,
begin
  simp only [conjugacy_classes_A5, finset.mem_def, multiset.mem_pmap,
    conjugacy_classes_A5_aux2] at h,
  rcases h with ⟨t, ht₁, ht₂⟩,
  rw [multiset.mem_map] at ht₁,
  rcases ht₁ with ⟨u, hu₁, hu₂⟩,
  have hx' : x ∈ multiset.map (λ (b : {b : A5 × A5 // b.2 * u.1 * b.2⁻¹ = b.1}), b.1.1) u.2,
  { simpa [ht₂.symm, hu₂] using hx },
  have hy' : y ∈ multiset.map (λ (b : {b : A5 × A5 // b.2 * u.1 * b.2⁻¹ = b.1}), b.1.1) u.2,
  { simpa [ht₂.symm, hu₂] using hy },
  cases multiset.mem_map.1 hx' with xc hxc,
  cases multiset.mem_map.1 hy' with yc hyc,
  exact is_conj_trans
    (is_conj_symm (show is_conj u.1 x, from hxc.2 ▸ ⟨_, xc.2⟩))
    (hyc.2 ▸ ⟨_, yc.2⟩)
end

lemma eq_bind_conjugacy_classes (s : finset (finset G))
  (h₁ : ∀ x, ∃ t ∈ s, x ∈ t)
  (h₂ : ∀ t ∈ s, ∀ x y ∈ t, is_conj x y) (I : finset G) [nI : normal_subgroup (↑I : set G)] :
  ∃ u ⊆ s, I = u.bind id :=
⟨(s.powerset.filter (λ u : finset (finset G), u.bind id ⊆ I)).bind id,
    (λ x, by simp only [finset.subset_iff, mem_bind, mem_filter, exists_imp_distrib, mem_powerset,
      and_imp, id.def] {contextual := tt}; tauto),
  le_antisymm
    (λ x hxI, let ⟨t, ht₁, ht₂⟩ := h₁ x in
      mem_bind.2 ⟨t, mem_bind.2 ⟨(s.powerset.filter (λ u : finset (finset G), u.bind id ⊆ I)).bind id,
          mem_filter.2 ⟨mem_powerset.2
            (λ u hu, let ⟨v, hv₁, hv₂⟩ := mem_bind.1 hu in
              mem_powerset.1 (mem_filter.1 hv₁).1 hv₂),
          λ y hy, let ⟨u, hu₁, hu₂⟩ := mem_bind.1 hy in
            let ⟨v, hv₁, hv₂⟩ := mem_bind.1 hu₁ in
            (mem_filter.1 hv₁).2 (mem_bind.2 ⟨u, hv₂, hu₂⟩)⟩,
        mem_bind.2 ⟨{t}, mem_filter.2 ⟨by simp [ht₁, finset.subset_iff],
            λ y hy, let ⟨u, hu₁, hu₂⟩ := mem_bind.1 hy in
              let ⟨z, hz⟩ := h₂ t ht₁ x y ht₂ (by simp * at *) in
              hz ▸ @normal_subgroup.normal G _ I.to_set nI _ hxI _⟩,
          by simp⟩⟩,
        ht₂⟩)
    (λ x, by simp only [finset.subset_iff, mem_bind, exists_imp_distrib, mem_filter, mem_powerset]; tauto)⟩

--local attribute [instance, priority 0] classical.dec

lemma simple_of_card_conjugacy_classes [fintype G] [decidable_eq G] (s : finset (finset G))
  (h₁ : ∀ x, ∃ t ∈ s, x ∈ t) (h₂ : ∀ t ∈ s, ∀ x y ∈ t, is_conj x y)
  (hs : (s.1.bind finset.val).nodup)
  (h₃ : ∀ t ≤ s.1.map finset.card, 1 ∈ t → t.sum ∣ fintype.card G → t.sum = 1 ∨ t.sum = fintype.card G) :
  simple_group G :=
by haveI := classical.dec; exact
⟨λ H iH,
  let I := (set.to_finset H) in
  have Ii : normal_subgroup (↑I : set G), by simpa using iH,
  let ⟨u, hu₁, hu₂⟩ :=
    @eq_bind_conjugacy_classes G _ _ _ s h₁ h₂ I Ii in
  have hInd : ∀ (x : finset G), x ∈ u → ∀ (y : finset G), y ∈ u → x ≠ y → id x ∩ id y = ∅,
    from λ x hxu y hyu hxy,
      begin
        rw multiset.nodup_bind at hs,
        rw [← finset.disjoint_iff_inter_eq_empty, finset.disjoint_left],
        exact multiset.forall_of_pairwise
          (λ (a b : finset G) (h : multiset.disjoint a.1 b.1),
          multiset.disjoint.symm h) hs.2 x (hu₁ hxu) y (hu₁ hyu) hxy
      end,
  have hci : card I = u.sum finset.card,
    by rw [hu₂, card_bind hInd]; refl,
  have hu1 : (1 : G) ∈ u.bind id, by exactI hu₂ ▸ is_submonoid.one_mem (↑I : set G),
  let ⟨v, hv₁, hv₂⟩ := mem_bind.1 hu1 in
  have hv : v = finset.singleton (1 : G),
    from finset.ext.2 $ λ a, ⟨λ hav, mem_singleton.2 $
        is_conj_one_right.1 (h₂ v (hu₁ hv₁) _ _ hv₂ hav),
      by simp [show (1 : G) ∈ v, from hv₂] {contextual := tt}⟩,
  have hci' : card I = 1 ∨ card I = fintype.card G,
    begin
      rw [hci],
      exact h₃ _ (multiset.map_le_map (show u.1 ≤ s.1,
        from (multiset.le_iff_subset u.2).2 hu₁))
          (multiset.mem_map.2 ⟨finset.singleton 1, hv ▸ hv₁, rfl⟩)
          (calc u.sum finset.card = card I : hci.symm
            ... = fintype.card (↑I : set G) : (set.card_fintype_of_finset' I (by simp)).symm
            ... ∣ fintype.card G : by exactI card_subgroup_dvd_card _)
    end,
    hci'.elim
      (λ hci', or.inl (set.ext (λ x,
        let ⟨y, hy⟩ := finset.card_eq_one.1 hci' in
        by resetI;
          simp only [I, finset.ext, set.mem_to_finset, finset.mem_singleton] at hy;
          simp [is_subgroup.mem_trivial, hy, (hy 1).1 (is_submonoid.one_mem H)])))
      (λ hci', or.inr $
        suffices I = finset.univ,
          by simpa [I, set.ext_iff, finset.ext] using this,
        finset.eq_of_subset_of_card_le (λ _, by simp) (by rw hci'; refl))⟩

lemma card_A5 : fintype.card A5 = 60 :=
(nat.mul_right_inj (show 2 > 0, from dec_trivial)).1 $
have 2 ≤ fintype.card (fin 5), from dec_trivial,
  by rw [card_alternating _ this]; simp; refl

lemma nodup_conjugacy_classes_A5_bind :
  (conjugacy_classes_A5.1.bind finset.val).nodup := dec_trivial

#eval (conjugacy_classes_A5.1.bind finset.val).card

lemma conjugacy_classes_A5_bind_eq_univ :
  conjugacy_classes_A5.bind (λ t, t) = univ :=
eq_of_subset_of_card_le (λ _, by simp)
  (calc card univ = 60 : card_A5
    ... = (conjugacy_classes_A5.bind id).card : dec_trivial
    ... ≤ _ : le_refl _)

lemma A5_simple : simple_group A5 :=
simple_of_card_conjugacy_classes conjugacy_classes_A5
  (λ x, mem_bind.1 $ by rw [conjugacy_classes_A5_bind_eq_univ]; simp)
  is_conj_conjugacy_classes_A5
  nodup_conjugacy_classes_A5_bind
  (by simp only [multiset.mem_powerset.symm, card_A5];
    exact dec_trivial)

#print axioms A5_simple

example : conj_classes_A5.1.map (finset.card ∘ prod.fst) = {1, 12, 12, 15, 20} := dec_trivial

--example : (@univ (alternating (fin 5))).nodup := dec_trivial

example : (conj_classes_A5.1.bind (λ s, s.1.1.map prod.fst)).nodup := dec_trivial

#eval (conj_classes_A5.1.bind (λ s, s.1.1.map prod.fst) = finset.univ.1 : bool)

--set_option class.instance_max_depth 100

instance alifha : decidable (∀ s : finset (alternating (fin 5) ×
  alternating (fin 5)) × alternating (fin 5), s ∈ conj_classes_A5 →
  ∀ (x : alternating (fin 5) × alternating (fin 5)), x ∈ s.1 →
  x.2 * s.2 * x.2⁻¹ = x.1) :=(@finset.decidable_dforall_finset _ conj_classes_A5
  (λ (s : finset (alternating (fin 5) ×
  alternating (fin 5)) × alternating (fin 5)) _,
  ∀ (x : alternating (fin 5) × alternating (fin 5)), x ∈ s.1 →
  x.2 * s.2 * x.2⁻¹ = x.1)
    (λ s hs, @finset.decidable_dforall_finset _ s.1 _ _))

#eval (∀ s : finset (alternating (fin 5) ×
  alternating (fin 5)) × alternating (fin 5), s ∈ conj_classes_A5 →
  ∀ (x : alternating (fin 5) × alternating (fin 5)), x ∈ s.1 →
  x.2 * s.2 * x.2⁻¹ = x.1 : bool)

def conj_classes_A5 : ∀ s : finset (alternating (fin 5) ×
  alternating (fin 5)) × alternating (fin 5), s ∈ conj_classes_A5 →
  ∀ (x : alternating (fin 5) × alternating (fin 5)), x ∈ s.1 →
  x.2 * s.2 * x.2⁻¹ = x.1 :=
dec_trivial

-- @of_as_true _ (@finset.decidable_dforall_finset _ conj_classes_A5
--   (λ (s : finset (alternating (fin 5) ×
--   alternating (fin 5)) × alternating (fin 5)) _,
--   ∀ (x : alternating (fin 5) × alternating (fin 5)), x ∈ s.1 →
--   x.2 * s.2 * x.2⁻¹ = x.1)
--     (λ s hs, @finset.decidable_dforall_finset _ s.1 _ _)) _root_.trivial




--example : multiset.nodup (@univ (alternating (fin 5)) _).1 := dec_trivial

--#eval x.map list.length

--#eval x.to_fun 3

#exit

set_option profiler true
#eval (conjugacy_classes' (alternating (fin 5))).1.map finset.card


instance : decidable_pred (is_cycle : perm α → Prop) :=
by dunfold is_cycle decidable_pred; apply_instance

local attribute [instance, priority 100] fintype_perm
local attribute [instance, priority 0] equiv.fintype
#print equiv.fintype

#eval (conjugacy_classes' (alternating (fin 5))).1.map finset.card

--example : (conjugacy_classes' (alternating (fin 5))).card = 5 := rfl

--#eval conjugacy_classes (quot.unquot (univ : finset (perm (fin 5))).1)