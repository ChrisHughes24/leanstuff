import ring_theory.adjoin_root order.zorn data.equiv.algebra algebra.direct_limit
import field_theory.subfield

universes u v w
open polynomial zorn set
variables (K : Type u) [discrete_field K]
noncomputable theory

def big_type := set (ℕ × polynomial K)

instance equiv.is_ring_hom {α β : Type*} [ring β] (e : α ≃ β) :
  @is_ring_hom α β (equiv.ring e) _ e :=
by split; simp [equiv.mul_def, equiv.add_def, equiv.one_def]

instance equiv.is_ring_hom.symm {α β : Type*} [ring β] (e : α ≃ β) :
  @is_ring_hom β α _ (equiv.ring e) e.symm :=
by letI := equiv.ring e; exact (show α ≃r β, from ⟨e, equiv.is_ring_hom e⟩).symm.2

local attribute [instance, priority 0] classical.dec

def big_type_map {L : Type*} [discrete_field L] (i : K → L) [is_ring_hom i]
  (h : ∀ l : L, algebraic K i l) (x : L) : ℕ × polynomial K :=
let f := classical.some (h x) in
⟨list.index_of x (quotient.out ((f.map i).roots.1)), f⟩

lemma list.index_of_inj {α : Type*} [decidable_eq α] {l : list α} {x y : α}
  (hx : x ∈ l) (hy : y ∈ l) (h : list.index_of x l = list.index_of y l) : x = y :=
have list.nth_le l (list.index_of x l) (list.index_of_lt_length.2 hx) =
    list.nth_le l (list.index_of y l) (list.index_of_lt_length.2 hy),
  by simp [h],
by simpa

lemma big_type_map_injective {L : Type*} [discrete_field L] (i : K → L) [is_ring_hom i]
  (h : ∀ l : L, algebraic K i l) : function.injective (big_type_map K i h) :=
λ x y hxy,
let f := classical.some (h x) in
let g := classical.some (h y) in
have hf : f ≠ 0 ∧ f.eval₂ i x = 0, from classical.some_spec (h x),
have hg : g ≠ 0 ∧ g.eval₂ i y = 0, from classical.some_spec (h y),
have hfg : f = g, from (prod.ext_iff.1 hxy).2,
have hfg' : list.index_of x (quotient.out ((f.map i).roots.1)) =
    list.index_of y (quotient.out ((f.map i).roots.1)),
  from (prod.ext_iff.1 hxy).1.trans (hfg.symm ▸ rfl),
have hx : x ∈ quotient.out ((f.map i).roots.1),
  from multiset.mem_coe.1 begin
    show x ∈ quotient.mk _,
    rw [quotient.out_eq, ← finset.mem_def, mem_roots (mt (map_eq_zero i).1 hf.1),
      is_root.def, eval_map, hf.2]
  end,
have hy : y ∈ quotient.out ((f.map i).roots.1),
  from multiset.mem_coe.1 begin
    show y ∈ quotient.mk _,
    rw [quotient.out_eq, ← finset.mem_def, mem_roots (mt (map_eq_zero i).1 hf.1),
      is_root.def, eval_map, hfg, hg.2]
  end,
list.index_of_inj hx hy hfg'

def embedding : K ↪ big_type K :=
⟨λ a, show set _, from {(0, X - C a)}, λ a b, by simp [C_inj]⟩

instance : discrete_field (set.range (embedding K)) :=
equiv.discrete_field (equiv.set.range _ (embedding K).2).symm

structure extensions : Type u :=
(carrier : set (big_type K))
[field : discrete_field ↥carrier]
(range_subset : set.range (embedding K) ⊆ carrier)
[is_ring_hom : is_ring_hom (inclusion (range_subset))]
(algebraic : ∀ x, algebraic _ (inclusion (range_subset)) x)
-- (lift : Π {α : Type u} [integral_domain α] (i : K → α)
--   [by exactI _root_.is_ring_hom i]
--   (h : by exactI ∀ f : polynomial K, 0 < degree f → ∃ x : α, f.eval₂ i x = 0),
--   carrier → α)
-- [lift_is_ring_hom : Π {α : Type u} [integral_domain α] (i : K → α)
--   [by exactI _root_.is_ring_hom i]
--   (h : by exactI ∀ f : polynomial K, 0 < degree f → ∃ x : α, f.eval₂ i x = 0),
--   by exactI is_ring_hom (lift i h)]

local attribute [instance] extensions.field extensions.is_ring_hom

instance : preorder (extensions K) :=
{ le := λ s t, ∃ hst : s.carrier ⊆ t.carrier, is_ring_hom (inclusion hst),
  le_refl := λ _, ⟨by refl, by simp [inclusion]; exact is_ring_hom.id⟩,
  le_trans := λ s t u ⟨hst₁, hst₂⟩ ⟨htu₁, htu₂⟩,
    ⟨set.subset.trans hst₁ htu₁,
      by resetI; convert is_ring_hom.comp (inclusion hst₁) (inclusion htu₁)⟩ }

private structure chain' (c : set (extensions K)) : Prop :=
(chain : chain (≤) c)

local attribute [class] chain'

lemma is_chain (c : set (extensions K)) [chain' _ c]: chain (≤) c :=
chain'.chain (by apply_instance)

section

variables (c : set (extensions K)) [hcn : nonempty c]
include c  hcn

variable [hcn' : chain' _ c]
include hcn'

instance chain_directed_order : directed_preorder c :=
⟨λ ⟨i, hi⟩ ⟨j, hj⟩, let ⟨k, hkc, hk⟩ := chain.directed_on
  (is_chain _ c) i hi j hj in ⟨⟨k, hkc⟩, hk⟩⟩

def chain_map (i j : c) (hij : i ≤ j) : i.1.carrier → j.1.carrier :=
inclusion (exists.elim hij (λ h _, h))

instance chain_ring_hom (i j : c) (hij : i ≤ j) : is_ring_hom (chain_map _ c i j hij) :=
exists.elim hij (λ _, id)

instance chain_directed_system : directed_system (λ i : c, i.1.carrier) (chain_map _ c) :=
by split; intros; simp [chain_map]

def chain_limit : Type u :=
  ring.direct_limit (λ i : c, i.1.carrier) (chain_map _ c)

lemma of_eq_of (x : big_type K) (i j : c) (hi : x ∈ i.1.carrier) (hj : x ∈ j.1.carrier) :
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map _ c) i ⟨x, hi⟩ =
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map _ c) j ⟨x, hj⟩ :=
have hij : i ≤ j ∨ j ≤ i,
  from show i.1 ≤ j.1 ∨ j.1 ≤ i.1, from chain.total (is_chain _ c) i.2 j.2,
hij.elim
  (λ hij, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map _ c) _
      _ _ _ hij,
    simp [chain_map, inclusion]
  end)
  (λ hij, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map _ c) _
      _ _ _ hij,
    simp [chain_map, inclusion]
  end)

lemma injective_aux (i j : c)
  (x y : ⋃ i : c, i.1.carrier) (hx : x.1 ∈ i.1.carrier) (hy : y.1 ∈ j.1.carrier) :
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map _ c) i ⟨x, hx⟩ =
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map _ c) j ⟨y, hy⟩ →
  x = y :=
have hij : i ≤ j ∨ j ≤ i,
  from show i.1 ≤ j.1 ∨ j.1 ≤ i.1, from chain.total (is_chain _ c) i.2 j.2,
have hinj : ∀ (i j : c) (hij : i ≤ j), function.injective (chain_map _ c i j hij),
  from λ _ _ _, inclusion_injective _,
hij.elim
  (λ hij h, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map _ c) _
      _ _ _ hij at h,
    simpa [chain_map, inclusion, subtype.coe_ext.symm] using ring.direct_limit.of_inj hinj j h,
  end)
  (λ hji h, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map _ c) _
      _ _ _ hji at h,
    simpa [chain_map, inclusion, subtype.coe_ext.symm] using ring.direct_limit.of_inj hinj i h,
  end)

def equiv_direct_limit : (⋃ (i : c), i.1.carrier) ≃
  ring.direct_limit (λ i : c, i.1.carrier) (chain_map _ c) :=
@equiv.of_bijective (⋃ i : c, i.1.carrier)
  (ring.direct_limit (λ i : c, i.1.carrier) (chain_map _ c))
  (λ x, ring.direct_limit.of _ _ (classical.some (set.mem_Union.1 x.2))
    ⟨_, classical.some_spec (set.mem_Union.1 x.2)⟩)
  ⟨λ x y, injective_aux _ _ _ _ _ _ _ _,
    λ x, let ⟨i, ⟨y, hy⟩, hy'⟩ := ring.direct_limit.exists_of x in
      ⟨⟨y, _, ⟨i, rfl⟩, hy⟩, begin
        convert hy',
        exact of_eq_of _ _ _ _ _ _ _
      end⟩⟩

instance Union_ring : discrete_field (⋃ i : c, i.1.carrier) :=
@equiv.discrete_field _ _ (equiv_direct_limit _ c)
  (field.direct_limit.discrete_field _ _)

instance is_ring_hom_Union (i : c) : is_ring_hom
  (inclusion (set.subset_Union (λ i : c, i.1.carrier) i)) :=
suffices inclusion (set.subset_Union (λ i : c, i.1.carrier) i) =
    ((equiv_direct_limit K c).symm ∘
    ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map _ c) i),
  by rw this; exact is_ring_hom.comp _ _,
funext $ λ ⟨_, _⟩,
  (equiv_direct_limit _ c).injective $
    by rw [function.comp_app, equiv.apply_symm_apply];
      exact of_eq_of _ _ _ _ _ _ _

instance is_ring_hom_range_Union [hc : nonempty c]
  (h : set.range (embedding K) ⊆ ⋃ i : c, i.1.carrier) :
  is_ring_hom (inclusion h) :=
let ⟨i⟩ := hc in
have h₁ : i.1.carrier ⊆ ⋃ i : c, i.1.carrier, from set.subset_Union _ i,
have h₂ : set.range (embedding K) ⊆ i.1.carrier, from i.1.range_subset,
have inclusion h = inclusion h₁ ∘ inclusion h₂, by simp [function.comp],
by rw this; exact is_ring_hom.comp _ _

end

lemma exists_algebraic_closure : ∃ m : extensions K, ∀ a, m ≤ a → a ≤ m :=
zorn
  (λ c hc, if h : nonempty c
    then by letI : chain' K c := ⟨hc⟩; exact
      ⟨⟨⋃ (i : c), i.1.carrier,
        let ⟨i⟩ := h in
        have hi : set.range (embedding K) ⊆ i.1.carrier,
          from extensions.range_subset _,
        set.subset.trans hi (set.subset_Union (λ i : c, i.1.carrier) i),
          begin
            rintros ⟨x, hx⟩,
            cases set.mem_Union.1 hx with i hi,
            convert @algebraic_comp (set.range (embedding K)) _ i.1.carrier
              (⋃ i : c, i.1.carrier) _ _
              (inclusion i.1.range_subset)
              (inclusion (set.subset_Union (λ i : c, i.1.carrier) (i : c))) _ _ _
              (i.1.algebraic ⟨x, hi⟩)
          end⟩,
        λ e he, ⟨set.subset_Union (λ i : c, i.1.carrier) ⟨e, he⟩,
          by apply_instance⟩⟩
    else
      have is_ring_hom (inclusion (set.subset.refl (set.range (embedding K)))) :=
      by convert is_ring_hom.id; funext; simp,
      by exactI ⟨⟨set.range (embedding K), by refl, λ _, by convert algebraic_id _ _; funext; simp⟩,
       λ a ha, (h ⟨⟨a, ha⟩⟩).elim⟩)
  (λ _ _ _, le_trans)

def algebraic_closure : Type u := (classical.some (exists_algebraic_closure K)).carrier

namespace algebraic_closure

instance : discrete_field (algebraic_closure K) :=
(classical.some (exists_algebraic_closure K)).field

def of : K → algebraic_closure K :=
inclusion (classical.some (exists_algebraic_closure K)).range_subset ∘
  (equiv.set.range _ (embedding K).2)

instance : is_ring_hom (of K) :=
by have h₁ := (classical.some (exists_algebraic_closure K)).is_ring_hom;
  have h₂ := equiv.is_ring_hom.symm (equiv.set.range _ (embedding K).2).symm;
  unfold of; exact @is_ring_hom.comp _ _ _ _ _ h₂ _ _ _ h₁

lemma of_algebraic (x : algebraic_closure K) : algebraic K (of K) x :=
let ⟨f, hf⟩ := (classical.some (exists_algebraic_closure K)).algebraic x in
⟨f.map (equiv.set.range _ (embedding K).2).symm,
  by rw [eval₂_map, of, function.comp]; simpa only [equiv.apply_symm_apply] using hf⟩

structure subfield_with_hom (L : Type v) (M : Type w) [discrete_field L]
  [discrete_field M] (f : K → L) (g : K → M) : Type (max u v w) :=
(carrier : set L)
[is_subfield : is_subfield carrier]
(map : carrier → M)
[is_ring_hom : by exactI is_ring_hom map]

local attribute [instance] subfield_with_hom.is_subfield subfield_with_hom.is_ring_hom

instance (L M f g) [discrete_field L] [discrete_field M] : preorder (subfield_with_hom K L M f g) :=
{ le := λ s t, ∃ h : s.carrier ⊆ t.carrier, ∀ x, t.map (inclusion h x) = s.map x,
  le_refl := λ _, ⟨set.subset.refl _, λ ⟨_, _⟩, rfl⟩,
  le_trans := λ s t u ⟨hst₁, hst₂⟩ ⟨htu₁, htu₂⟩,
    ⟨set.subset.trans hst₁ htu₁,
      λ _, by rw [← hst₂, ← htu₂, inclusion_inclusion]⟩ }

def thing {L : Type v} {M : Type w} [discrete_field L] [discrete_field M]
  (i : K → L) (j : K → M) [is_ring_hom i] [is_ring_hom j]
  (hL : ∀ x, algebraic K i x) (hM : ∀ f : polynomial K, 0 < degree f → ∃ x, f.eval₂ i x = 0) :
  ∃ s : subfield_with_hom K L M i j, ∀ t, s ≤ t → t ≤ s :=
zorn
  (λ c hc, if hcn : c = ∅
    then ⟨{ carrier := set.range i,
        map := j ∘ (ring_equiv.set.range i (is_field_hom.injective _)).symm.to_equiv,
        is_ring_hom := is_ring_hom.comp _ _ },
      by simp [hcn]⟩
    else let ⟨i, hi⟩ := set.exists_mem_of_ne_empty hcn in
      have nonempty c, from ⟨⟨i, hi⟩⟩,
      ⟨{ carrier := ⋃ i : c, i.1.carrier,
        is_subfield := by exactI is_subfield_Union_of_directed _
          (begin
            rintros ⟨i, hi⟩ ⟨j, hj⟩,
            cases hc.directed hi hj with z hz,
            exact ⟨⟨z, hz.1⟩, hz.2.1.fst, hz.2.2.fst⟩
          end),
        map := λ x, (classical.some (set.mem_Union.1 x.2)).1.map
          ⟨x, classical.some_spec (set.mem_Union.1 x.2)⟩,
        is_ring_hom :=
          { map_one := _,
            map_mul := begin
              assume x y,

            end,
            map_add := _ } }, _⟩)
  (λ _ _ _, le_trans)


end algebraic_closure
