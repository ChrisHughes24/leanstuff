import ring_theory.adjoin_root data.equiv.algebra algebra.direct_limit
import set_theory.schroeder_bernstein

universes u v w
open polynomial zorn set function
variables (K : Type u) [discrete_field K]
noncomputable theory

instance equiv.is_ring_hom {α β : Type*} [ring β] (e : α ≃ β) :
  @is_ring_hom α β (equiv.ring e) _ e :=
by split; simp [equiv.mul_def, equiv.add_def, equiv.one_def]

instance equiv.is_ring_hom.symm {α β : Type*} [ring β] (e : α ≃ β) :
  @is_ring_hom β α _ (equiv.ring e) e.symm :=
by letI := equiv.ring e; exact (show α ≃r β, from ⟨e, equiv.is_ring_hom e⟩).symm.2

inductive in_algebraic_closure {L : Type v} [discrete_field L] (i : K → L) : L → Prop
| of_field : ∀ x, in_algebraic_closure (i x)
| root     : ∀ (l : L) (f : polynomial L), f ≠ 0 → (∀ n : ℕ, in_algebraic_closure (f.coeff n)) →
  is_root f l → in_algebraic_closure l

def algebraic {L : Type v} [comm_ring L] (i : K → L) (x : L) : Prop :=
∃ f : polynomial K, f ≠ 0 ∧ f.eval₂ i x = 0

class is_algebraically_closed :=
(exists_root : ∀ f : polynomial K, 0 < degree f → ∃ x, is_root f x)

lemma algebraic_comp {L M : Type*} [comm_ring L] [decidable_eq L] [comm_ring M] [decidable_eq M]
  (i : K → L) (j : L → M) [is_ring_hom i] [is_ring_hom j] {x : L} :
  algebraic K i x → algebraic K (j ∘ i) (j x) :=
λ ⟨f, hf⟩, ⟨f, hf.1, by rw [← eval_map, function.comp, ← polynomial.map_map i j, eval_map,
    eval₂_hom, eval_map, hf.2, is_ring_hom.map_zero j]⟩

lemma algebraic_id (x : K) : algebraic K id x :=
⟨X - C x, ne_zero_of_monic (monic_X_sub_C _), by simp⟩

lemma algebraic_equiv {L : Type*} [discrete_field L] (e : K ≃ L) [is_ring_hom e] (x : L) : 
  algebraic K e x :=
⟨X - C (e.symm x), ne_zero_of_monic (monic_X_sub_C _), 
  by rw [← eval_map, map_sub, map_X, map_C, equiv.apply_symm_apply,
      eval_sub, eval_X, eval_C, sub_self]⟩

lemma algebraic_adjoin_root (f : polynomial K) [irreducible f] :
  ∀ x, algebraic K (adjoin_root.of : K → adjoin_root f) x := sorry

lemma algebraic_comp' {L M : Type*} [discrete_field L] [discrete_field M]
  (i : K → L) (j : L → M) [is_field_hom i] [is_field_hom j] :
  (∀ x, algebraic K i x) → (∀ x, algebraic L j  x) → ∀ x, algebraic K (j ∘ i) x := sorry

section classical

local attribute [instance, priority 1] classical.dec

def big_type := set (ℕ × polynomial K)

def big_type_map {L : Type*} [discrete_field L] (i : K → L) [is_ring_hom i]
  (h : ∀ l : L, algebraic K i l) (x : L) : ℕ × polynomial K :=
let f := classical.some (h x) in
⟨list.index_of x (quotient.out ((f.map i).roots.1)), f⟩

lemma big_type_map_injective {L : Type*} [discrete_field L] (i : K → L) [is_ring_hom i]
  (h : ∀ l : L, algebraic K i l) : injective (big_type_map K i h) :=
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
(list.index_of_inj hx hy).1 hfg'

lemma bembedding : K ↪ big_type K :=
⟨λ a, show set _, from {(0, X - C a)}, λ a b, by simp [C_inj]⟩

instance : discrete_field (set.range (bembedding K)) :=
equiv.discrete_field (equiv.set.range _ (bembedding K).2).symm

structure extension : Type (u+1) :=
(carrier : set (big_type K))
[field : discrete_field ↥carrier]
(range_subset : set.range (bembedding K) ⊆ carrier)
[is_field_hom : is_field_hom (inclusion range_subset)]
(algebraic : ∀ x, algebraic _ (inclusion (range_subset)) x)
(lift : Π {α : Type u} [discrete_field α] (i : set.range (bembedding K) → α)
  [by exactI _root_.is_field_hom i] [is_algebraically_closed α],
  carrier → α)
(lift_is_field_hom : ∀ {α : Type u} [discrete_field α] (i : set.range (bembedding K) → α)
  [by exactI _root_.is_field_hom i] [is_algebraically_closed α],
  by exactI _root_.is_field_hom (lift i))
(lift_comp : ∀ {α : Type u} [discrete_field α] (i : set.range (bembedding K) → α)
  [by exactI _root_.is_field_hom i] [is_algebraically_closed α] (x),
  by exactI lift i (inclusion range_subset x) = i x)

local attribute [instance] extension.field extension.is_field_hom extension.lift_is_field_hom

instance : preorder (extension K) :=
{ le := λ s t, ∃ hst : s.carrier ⊆ t.carrier, is_field_hom (inclusion hst)
    ∧ ∀ {α : Type u} [discrete_field α] (i : set.range (bembedding K) → α)
    [by exactI _root_.is_field_hom i] [by exactI is_algebraically_closed α] (x : s.carrier),
    by exactI s.lift i x = t.lift i (inclusion hst x),
  le_refl := λ _, ⟨by refl, by simp [inclusion]; exact is_ring_hom.id,
    by intros; simp [inclusion, subtype.coe_eta]⟩,
  le_trans := λ s t u ⟨hst₁, hst₂, hst₃⟩ ⟨htu₁, htu₂, htu₃⟩,
    ⟨set.subset.trans hst₁ htu₁,
      by resetI; convert is_ring_hom.comp (inclusion hst₁) (inclusion htu₁),
      by intros; rw [hst₃, htu₃, inclusion_inclusion]⟩ }

private structure chain' (c : set (extension K)) : Prop :=
(chain : chain (≤) c)

local attribute [class] chain'

lemma is_chain (c : set (extension K)) [chain' _ c]: chain (≤) c :=
chain'.chain (by apply_instance)

section

variables (c : set (extension K)) [hcn : nonempty c]
include c  hcn

variable [hcn' : chain' _ c]
include hcn'

instance chain_directed_order : directed_preorder c :=
⟨λ ⟨i, hi⟩ ⟨j, hj⟩, let ⟨k, hkc, hk⟩ := chain.directed_on
  (is_chain _ c) i hi j hj in ⟨⟨k, hkc⟩, hk⟩⟩

def chain_map (i j : c) (hij : i ≤ j) : i.1.carrier → j.1.carrier :=
inclusion (exists.elim hij (λ h _, h))

instance chain_field_hom (i j : c) (hij : i ≤ j) : is_field_hom (chain_map _ c i j hij) :=
exists.elim hij (λ _, and.left)

instance chain_directed_system : directed_system (λ i : c, i.1.carrier) (chain_map _ c) :=
by split; intros; simp [chain_map]

def chain_limit : Type (u+1) :=
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
have hinj : ∀ (i j : c) (hij : i ≤ j), injective (chain_map _ c i j hij),
  from λ _ _ _, is_field_hom.injective _,
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

instance Union_field : discrete_field (⋃ i : c, i.1.carrier) :=
@equiv.discrete_field _ _ (equiv_direct_limit _ c)
  (field.direct_limit.discrete_field _ _)

instance is_field_hom_Union (i : c) : is_field_hom
  (inclusion (set.subset_Union (λ i : c, i.1.carrier) i)) :=
suffices inclusion (set.subset_Union (λ i : c, i.1.carrier) i) =
    ((equiv_direct_limit K c).symm ∘
    ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map _ c) i),
  by rw this; exact is_ring_hom.comp _ _,
funext $ λ ⟨_, _⟩,
  (equiv_direct_limit _ c).injective $
    by rw [function.comp_app, equiv.apply_symm_apply];
      exact of_eq_of _ _ _ _ _ _ _

instance is_field_hom_range_Union [hc : nonempty c]
  (h : set.range (bembedding K) ⊆ ⋃ i : c, i.1.carrier) :
  is_field_hom (inclusion h) :=
let ⟨i⟩ := hc in
have h₁ : i.1.carrier ⊆ ⋃ i : c, i.1.carrier, from set.subset_Union _ i,
have h₂ : set.range (bembedding K) ⊆ i.1.carrier, from i.1.range_subset,
have inclusion h = inclusion h₁ ∘ inclusion h₂, by simp [function.comp],
by rw this; exact is_ring_hom.comp _ _

def chain_lift [nonempty c] (α : Type u) [discrete_field α] (i : set.range (bembedding K) → α)
  [is_field_hom i] [is_algebraically_closed α] :
  (⋃ i : c, i.1.carrier) → α :=
(ring.direct_limit.lift (λ j : c, j.1.carrier) (chain_map _ c) _
  (λ j : c, j.1.lift i) (λ i j ⟨_, _, h⟩, by introsI; rw [h, chain_map])) ∘
  (equiv_direct_limit K c)

def is_field_hom_chain_lift [nonempty c] (α : Type u) [discrete_field α]
  (i : set.range (bembedding K) → α) [is_field_hom i]
  [is_algebraically_closed α] : is_field_hom (chain_lift K c α i) :=
is_ring_hom.comp _ _

end

lemma exists_algebraic_closure : ∃ m : extension K, ∀ a, m ≤ a → a ≤ m :=
by letI := classical.dec; exact
zorn
  (λ c hc, if h : nonempty c
    then by letI : chain' K c := ⟨hc⟩; exact
      ⟨{carrier := ⋃ (i : c), i.1.carrier,
        range_subset := let ⟨i⟩ := h in
          have hi : set.range (bembedding K) ⊆ i.1.carrier,
            from extension.range_subset _,
          set.subset.trans hi (set.subset_Union (λ i : c, i.1.carrier) i),
        algebraic := begin
            rintros ⟨x, hx⟩,
            cases set.mem_Union.1 hx with i hi,
            convert @algebraic_comp (set.range (bembedding K)) _ i.1.carrier
              (⋃ i : c, i.1.carrier) _ _ _ _
              (inclusion i.1.range_subset)
              (inclusion (set.subset_Union (λ i : c, i.1.carrier) (i : c))) _ _ _
              (i.1.algebraic ⟨x, hi⟩)
          end,
        lift := chain_lift _ c,
        lift_is_field_hom := is_field_hom_chain_lift K c,
        lift_comp := begin
            intros,
            dunfold chain_lift equiv_direct_limit,
            simp,
            erw extension.lift_comp
          end },
      λ e he, ⟨set.subset_Union (λ i : c, i.1.carrier) ⟨e, he⟩,
        by apply_instance,
        begin
          intros,
          dsimp [chain_lift, equiv_direct_limit],
          erw [ring.direct_limit.lift_of],
          cases chain.total (is_chain _ c) he (classical.some (set.mem_Union.1
            (set.subset_Union (λ i : c, i.1.carrier) ⟨e, he⟩ x.2))).2 with h h,
          { rw (classical.some_spec h).2, refl },
          { erw (classical.some_spec h).2, cases x, refl }
        end⟩⟩
    else
      have is_field_hom (inclusion (set.subset.refl (set.range (bembedding K)))) :=
      by convert is_ring_hom.id; funext; simp,
      by exactI ⟨⟨set.range (bembedding K), by refl,
          λ _, by convert algebraic_id _ _; funext; simp, λ _ _ i _ _, i,
          by introsI; apply_instance, by simp [inclusion]⟩,
        λ a ha, (h ⟨⟨a, ha⟩⟩).elim⟩)
  (λ _ _ _, le_trans)

def closed_extension := classical.some (exists_algebraic_closure K)

def algebraic_closure : Type u := ((classical.some (exists_algebraic_closure K))).carrier

end classical

namespace algebraic_closure

instance : discrete_field (algebraic_closure K) :=
{ has_decidable_eq := classical.dec_eq _,
  ..(classical.some (exists_algebraic_closure K)).field }

def of_aux : K → set.range (bembedding K) :=
equiv.set.range _ (bembedding K).2

lemma of_aux.is_field_hom : is_ring_hom (of_aux K) :=
equiv.is_ring_hom.symm (equiv.set.range _ (bembedding K).2).symm

def of_aux_symm : set.range (bembedding K) → K :=
(equiv.set.range _ (bembedding K).2).symm

lemma of_aux_symm.is_field_hom : is_ring_hom (of_aux_symm K) :=
equiv.is_ring_hom (equiv.set.range _ (bembedding K).2).symm

local attribute [instance] of_aux.is_field_hom of_aux_symm.is_field_hom

def of : K → algebraic_closure K :=
inclusion (classical.some (exists_algebraic_closure K)).range_subset ∘ 
(of_aux K)

instance : is_ring_hom (of K) :=
begin 
  haveI h₁ := (classical.some (exists_algebraic_closure K)).is_field_hom,
  letI h₂ : ring (classical.some (exists_algebraic_closure K)).carrier :=
    show ring (algebraic_closure K), by apply_instance,
  unfold of,
  exact @is_ring_hom.comp _ _ _ _ _ _ _ _ _ h₁
end

lemma of_algebraic_aux (x : algebraic_closure K) : 
  @algebraic (set.range (bembedding K)) _ (algebraic_closure K) _
  (inclusion (classical.some (exists_algebraic_closure K)).range_subset) x :=
(classical.some (exists_algebraic_closure K)).algebraic x

lemma of_algebraic (x : algebraic_closure K) : algebraic K (of K) x :=
let ⟨f, hf⟩ := (classical.some (exists_algebraic_closure K)).algebraic x in
⟨f.map (of_aux_symm K), mt (map_eq_zero _).1 hf.1,
  calc eval₂ (of K) x (f.map (of_aux_symm K)) = eval₂ (λ x, of K (of_aux_symm K x)) x f :
    sorry

  ... = 0 : sorry
  ⟩
 -- eval₂_map (of_aux_symm K) (of K) x).trans _

def lift_aux {L : Type u} [discrete_field L] (i : set.range (bembedding K) → L)
  [is_field_hom i] [is_algebraically_closed L] :
  algebraic_closure K → L :=
(classical.some (exists_algebraic_closure K)).lift i

lemma lift_aux.is_field_hom {L : Type u} [discrete_field L] (i : set.range (bembedding K) → L)
  [is_field_hom i] [is_algebraically_closed L] : is_field_hom (lift_aux K i) :=
(classical.some (exists_algebraic_closure K)).lift_is_field_hom _

local attribute [instance] lift_aux.is_field_hom

section map

local attribute [instance] classical.dec

lemma map_aux {X : Type u} {Y : Type v} {Z : Type w} (fxy : X ↪ Y) (fxz : X ↪ Z)
  (hYZ : (Z ↪ Y) → false) : ↥-range fxy.1 ↪ ↥-range fxz.1 :=
classical.choice $ or.resolve_left embedding.total $
  λ ⟨f⟩, hYZ $
    calc Z ↪ range fxz ⊕ ↥-range fxz :
      (equiv.set.sum_compl _).symm.to_embedding
    ... ↪ range fxy ⊕ ↥-range fxy :
      embedding.sum_congr
        (((equiv.set.range _ fxz.2).symm.to_embedding).trans
          (equiv.set.range _ fxy.2).to_embedding)
        f
    ... ↪ Y : (equiv.set.sum_compl _).to_embedding

def map {X : Type u} {Y : Type v} {Z : Type w} (fxy : X ↪ Y) (fxz : X ↪ Z)
  (hYZ : (Z ↪ Y) → false) : Y ↪ Z :=
calc Y ↪ range fxy ⊕ ↥-range fxy : (equiv.set.sum_compl _).symm.to_embedding
... ↪ range fxz ⊕ ↥-range fxz : embedding.sum_congr
  ((equiv.set.range _ fxy.2).symm.to_embedding.trans
    (equiv.set.range _ fxz.2).to_embedding)
  (map_aux fxy fxz hYZ)
... ↪ Z : (equiv.set.sum_compl _).to_embedding

lemma map_commutes {X : Type u} {Y : Type v} {Z : Type w}  (fxy : X ↪ Y) (fxz : X ↪ Z)
  (hYZ : (Z ↪ Y) → false) (x : X) : map fxy fxz hYZ (fxy x) = fxz x :=
have (⟨fxy x, mem_range_self _⟩ : range fxy) = equiv.set.range _ fxy.2 x, from rfl,
begin
  dsimp only [map, embedding.trans_apply, equiv.trans_apply, function.comp,
    equiv.to_embedding_coe_fn],
  simp only [equiv.set.sum_compl_symm_apply_of_mem (mem_range_self _),
    embedding.sum_congr_apply_inl, equiv.set.sum_compl_apply_inl,
    embedding.trans_apply, equiv.to_embedding_coe_fn, this, equiv.symm_apply_apply],
  refl
end

end map

section adjoin_root
variables (f : polynomial (algebraic_closure K)) [hif : irreducible f]
include hif

instance adjoin_root_algebraic_closure.field : 
  discrete_field (adjoin_root f) := by apply_instance

instance adjoin_root_algebraic_closure.is_ring_hom : 
  is_ring_hom (@adjoin_root.of _ _ _ f) := by apply_instance

instance algebraic_closure_adjoin_root_comp.is_ring_hom : 
  is_ring_hom (@adjoin_root.of _ _ _ f ∘ of K) := is_ring_hom.comp _ _

def adjoin_root.of_embedding : algebraic_closure K ↪ adjoin_root f :=
⟨adjoin_root.of, is_field_hom.injective _⟩

def adjoin_root_extension_map : adjoin_root f ↪ big_type K :=
(map (adjoin_root.of_embedding K f) 
    ⟨subtype.val, subtype.val_injective⟩ 
  (λ i, cantor_injective _ (show big_type K ↪ ℕ × polynomial K,
    from i.trans ⟨big_type_map K (@adjoin_root.of _ _ _ f ∘ of K)
        (algebraic_comp' K _ _ (of_algebraic K) (algebraic_adjoin_root _ f)), 
      big_type_map_injective _ _ _⟩).2))

lemma adjoin_root_extension_map_apply (x : algebraic_closure K) : 
  (adjoin_root_extension_map K f) (@adjoin_root.of _ _ _ f x) = x.val :=
map_commutes _ _ _ _

lemma closure_subset_adjoin_root :
  (closed_extension K).carrier ⊆ set.range (adjoin_root_extension_map K f) :=
(λ x h, ⟨adjoin_root.of_embedding K f ⟨x, h⟩, 
  show (adjoin_root_extension_map K f) 
      (adjoin_root.of_embedding K f ⟨x, h⟩) = 
      (⟨x, h⟩ : algebraic_closure K).val, 
    from map_commutes _ _ _ _⟩)

lemma adjoin_root_range_subset : 
  (set.range (bembedding K)) ⊆ set.range (adjoin_root_extension_map K f) :=
set.subset.trans 
  (classical.some (exists_algebraic_closure K)).range_subset 
  (closure_subset_adjoin_root K f)

lemma adjoin_root_inclusion_eq : 
  inclusion (adjoin_root_range_subset K f) = 
  (equiv.set.range _ (adjoin_root_extension_map K f).2) ∘ 
  (@adjoin_root.of (algebraic_closure K) _ _ f) ∘ 
  inclusion (classical.some (exists_algebraic_closure K)).range_subset :=
funext $ λ x, subtype.eq $ 
  by simp [inclusion, function.comp, adjoin_root_extension_map_apply]

lemma adjoin_root_inclusion_eq' :
  inclusion (closure_subset_adjoin_root K f) = 
  (equiv.set.range _ (adjoin_root_extension_map K f).2) ∘
  (@adjoin_root.of (algebraic_closure K) _ _ f) :=
funext $ λ x, subtype.eq $ 
  by simp [inclusion, function.comp, adjoin_root_extension_map_apply]; refl

instance adjoin_root_range.discrete_field : 
  discrete_field (set.range (adjoin_root_extension_map K f)) :=
equiv.discrete_field (equiv.set.range _ (embedding.inj _)).symm

instance adjoin_root_inclusion.is_ring_hom : 
  is_ring_hom (inclusion (adjoin_root_range_subset K f)) :=
begin
  letI := (classical.some (exists_algebraic_closure K)).is_field_hom,
  rw [adjoin_root_inclusion_eq, ← equiv.symm_symm (equiv.set.range _ _)],
  exact @is_ring_hom.comp _ _ _ _ _ (is_ring_hom.comp _ _) _ _ _ 
    (equiv.is_ring_hom.symm _)
end
--set_option eqn_compiler.zeta true

def adjoin_root_lift {α : Type u} [_inst_2_1 : discrete_field α] (i : (range ⇑(bembedding K)) → α)
  [is_field_hom i] [is_algebraically_closed α] :
  (range ⇑(adjoin_root_extension_map K f)) → α :=
begin
  have h : _ := is_algebraically_closed.exists_root 
    (f.map (lift_aux K i)) 
    (by rw degree_map; exact degree_pos_of_ne_zero_of_nonunit 
      (nonzero_of_irreducible hif) hif.1),
  exact adjoin_root.lift (lift_aux K i) (classical.some h) (by rw [← eval_map]; 
    exact (classical.some_spec h)) ∘ 
  (equiv.set.range _ (adjoin_root_extension_map K f).2).symm
end

lemma adjoin_root_lift.is_ring_hom {α : Type u} [_inst_2_1 : discrete_field α] 
  (i : (range ⇑(bembedding K)) → α) [is_field_hom i] [is_algebraically_closed α] :
  is_field_hom (adjoin_root_lift _ f i) :=
begin
  letI := equiv.is_ring_hom.symm (equiv.set.range _ (adjoin_root_extension_map K f).2),
  dsimp [adjoin_root_lift],
  rw [← equiv.symm_symm (equiv.set.range _ _)],
  exact is_ring_hom.comp _ _
end

def adjoin_root_extension : extension K :=
{ carrier := set.range (adjoin_root_extension_map K f),
  range_subset := adjoin_root_range_subset _ _,
  algebraic := begin
    letI := (classical.some (exists_algebraic_closure K)).is_field_hom,
    rw [adjoin_root_inclusion_eq, ← equiv.symm_symm (equiv.set.range _ _)],
    refine @algebraic_comp' _ _ _ _ _ _ _ _ 
      (is_ring_hom.comp _ _) (by convert equiv.is_ring_hom.symm _) _ _,
    { exact @algebraic_comp' _ _ _ _ _ 
        _ _ _ _ _ (of_algebraic_aux _) (algebraic_adjoin_root _ f) },
    { exact algebraic_equiv _ _ }
  end,
  lift := @adjoin_root_lift K _ _ _,
  lift_is_field_hom := @adjoin_root_lift.is_ring_hom K _ _ _,
  lift_comp := begin
    intros,
    dsimp [adjoin_root_lift, function.comp],
    have : inclusion (adjoin_root_range_subset K f) x =  
      equiv.set.range _ (adjoin_root_extension_map K f).2 
        (adjoin_root.of 
          (inclusion (classical.some (exists_algebraic_closure K)).range_subset x)),
      by rw [adjoin_root_inclusion_eq],
    erw [this, equiv.symm_apply_apply, adjoin_root.lift_of],
    exactI (classical.some (exists_algebraic_closure K)).lift_comp _ _
  end }

example : 1 + 1 = 2 := rfl

instance adjoin_root_extension.field : discrete_field (adjoin_root_extension K f).carrier := 
extension.field _

local attribute [instance] extension.field extension.is_field_hom extension.lift_is_field_hom

lemma closed_extension_le_adjoin_root_extension : 
  closed_extension K ≤ adjoin_root_extension K f :=
by letI : discrete_field (closed_extension K).carrier := extension.field _; exact
⟨closure_subset_adjoin_root K f, by rw [adjoin_root_inclusion_eq'];
  exact is_ring_hom.comp _ _, begin
  introsI,

end⟩

instance : is_algebraically_closed (algebraic_closure K) :=
⟨λ f hf0, let ⟨g, hg⟩ := is_noetherian_ring.exists_irreducible_factor 
    (show ¬ is_unit f, from λ h, by rw [is_unit_iff_degree_eq_zero] at h;
      rw h at hf0; exact lt_irrefl _ hf0) 
    (λ h, by rw [← degree_eq_bot] at h;
      rw h at hf0; exact absurd hf0 dec_trivial) in
  begin
    letI := hg.1,
    have := classical.some_spec (exists_algebraic_closure K)
      (adjoin_root_extension K g),
  
  end⟩ 

end adjoin_root

end algebraic_closure
