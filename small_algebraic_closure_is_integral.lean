import ring_theory.adjoin_root data.equiv.algebra algebra.direct_limit
import set_theory.schroeder_bernstein field_theory.subfield
import ring_theory.integral_closure ring_theory.algebra

universes u v w
open polynomial zorn set function
variables {K : Type u} [discrete_field K]
noncomputable theory

instance equiv.is_ring_hom {α β : Type*} [ring β] (e : α ≃ β) :
  @is_ring_hom α β (equiv.ring e) _ e :=
by split; simp [equiv.mul_def, equiv.add_def, equiv.one_def]

instance equiv.is_ring_hom.symm {α β : Type*} [ring β] (e : α ≃ β) :
  @is_ring_hom β α _ (equiv.ring e) e.symm :=
by letI := equiv.ring e; exact (show α ≃r β, from ⟨e, equiv.is_ring_hom e⟩).symm.2

namespace algebraic_closure
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
end algebraic_closure

class is_algebraically_closed (K : Type u) [nonzero_comm_ring K] [decidable_eq K] :=
(exists_root : ∀ f : polynomial K, 0 < degree f → ∃ x, is_root f x)

-- lemma algebraic_comp {L M : Type*} [comm_ring L] [decidable_eq L] [comm_ring M] [decidable_eq M]
--   (i : K → L) (j : L → M) [is_ring_hom i] [is_ring_hom j] {x : L} :
--   algebraic K i x → algebraic K (j ∘ i) (j x) :=
-- λ ⟨f, hf⟩, ⟨f, hf.1, by rw [← eval_map, function.comp, ← polynomial.map_map i j, eval_map,
--     eval₂_hom, eval_map, hf.2, is_ring_hom.map_zero j]⟩

-- lemma algebraic_id (x : K) : algebraic K id x :=
-- ⟨X - C x, ne_zero_of_monic (monic_X_sub_C _), by simp⟩

-- lemma algebraic_equiv {L : Type*} [discrete_field L] (e : K ≃ L) [is_ring_hom e] (x : L) :
--   algebraic K e x :=
-- ⟨X - C (e.symm x), ne_zero_of_monic (monic_X_sub_C _),
--   by rw [← eval_map, map_sub, map_X, map_C, equiv.apply_symm_apply,
--       eval_sub, eval_X, eval_C, sub_self]⟩

-- lemma algebraic_adjoin_root (f : polynomial K) [irreducible f] :
--   ∀ x, algebraic K (adjoin_root.of : K → adjoin_root f) x := sorry

-- lemma algebraic_comp' {L M : Type*} [discrete_field L] [discrete_field M]
--   (i : K → L) (j : L → M) [is_field_hom i] [is_field_hom j] :
--   (∀ x, algebraic K i x) → (∀ x, algebraic L j  x) → ∀ x, algebraic K (j ∘ i) x := sorry

section classical

local attribute [instance, priority 1] classical.dec

/-- The `big_type` with cardinality strictly larger than any algebraic extension -/
def big_type (K : Type u) [discrete_field K] := set (ℕ × polynomial K)

def algebraic_embedding_aux {L : Type*} [discrete_field L] [algebra K L]
  (h : ∀ l : L, is_integral K l) (x : L) : ℕ × polynomial K :=
let f := classical.some (h x) in
⟨list.index_of x (quotient.out ((f.map (algebra_map L)).roots.1)), f⟩

lemma algebraic_embedding_aux_injective
  {L : Type*} [discrete_field L] [algebra K L]
  (h : ∀ l : L, is_integral K l) : injective (algebraic_embedding_aux h) :=
λ x y hxy,
let f := classical.some (h x) in
let g := classical.some (h y) in
have hf : monic f ∧ aeval K L x f = 0, from classical.some_spec (h x),
have hg : monic g ∧ aeval K L y g = 0, from classical.some_spec (h y),
have hfg : f = g, from (prod.ext_iff.1 hxy).2,
have hfg' : list.index_of x (quotient.out ((f.map (algebra_map L)).roots.1)) =
    list.index_of y (quotient.out ((f.map (algebra_map L)).roots.1)),
  from (prod.ext_iff.1 hxy).1.trans (hfg.symm ▸ rfl),
have hx : x ∈ quotient.out ((f.map (algebra_map L)).roots.1),
  from multiset.mem_coe.1 begin
    show x ∈ quotient.mk _,
    rw [quotient.out_eq, ← finset.mem_def, mem_roots (mt (map_eq_zero (algebra_map L)).1
      (ne_zero_of_monic hf.1)), is_root.def, eval_map, ← aeval_def, hf.2],
  end,
have hy : y ∈ quotient.out ((g.map (algebra_map L)).roots.1),
  from multiset.mem_coe.1 begin
    show y ∈ quotient.mk _,
    rw [quotient.out_eq, ← finset.mem_def, mem_roots (mt (map_eq_zero (algebra_map L)).1
      (ne_zero_of_monic hg.1)), is_root.def, eval_map, ← aeval_def, hg.2],
  end,
(list.index_of_inj hx (by rwa hfg)).1 hfg'

lemma injective_eq {α : Sort*} : injective (eq : α → α → Prop) :=
λ _ _ h, h.symm ▸ rfl

def algebraic_embedding_big_type {L : Type*} [discrete_field L] [algebra K L]
  (h : ∀ l : L, is_integral K l) : L ↪ big_type K :=
⟨_, injective_comp injective_eq $ algebraic_embedding_aux_injective h⟩

def algebraic_embedding {L : Type*} [discrete_field L] [algebra K L]
  (h : ∀ l : L, is_integral K l) : L ↪ ℕ × polynomial K :=
⟨_, algebraic_embedding_aux_injective h⟩

def bembedding (K : Type u) [discrete_field K] : K ↪ big_type K :=
⟨λ a, show set _, from {(0, X - C a)}, λ a b, by simp [C_inj]⟩

instance : discrete_field (set.range (bembedding K)) :=
equiv.discrete_field (equiv.set.range _ (bembedding K).2).symm

structure extension (K : Type u) [discrete_field K] : Type u :=
(carrier : set (big_type K))
[field : discrete_field ↥carrier]
[algebra : algebra K ↥carrier]
--(algebraic : ∀ x : carrier, is_integral K x)

local attribute [instance] extension.field extension.algebra

def base_extension (K : Type u) [discrete_field K] : extension K :=
{ carrier := set.range (bembedding K),
  algebra := algebra.of_ring_hom (equiv.set.range _ (bembedding K).2).symm.symm
    (equiv.is_ring_hom.symm _) }

-- instance : preorder (extension K) :=
-- { le := λ L M, ∃ hLM : L.carrier ⊆ M.carrier, is_ring_hom (inclusion hLM)
--     ∧ ∀ x : K, inclusion hLM (algebra_map L.carrier x) = algebra_map M.carrier x,
--   le_refl := λ _, ⟨set.subset.refl _, by convert is_ring_hom.id; ext; simp, by simp⟩,
--   le_trans := λ L M N ⟨hLM₁, hLM₂, hLM₃⟩ ⟨hMN₁, hMN₂, hMN₃⟩, ⟨set.subset.trans hLM₁ hMN₁,
--     by resetI; convert is_ring_hom.comp (inclusion hLM₁) (inclusion hMN₁),
--     λ _, by rw [← hMN₃, ← hLM₃, inclusion_inclusion]⟩ }

instance : preorder (extension K) :=
{ le := λ L M, ∃ hLM : L.carrier ⊆ M.carrier, is_ring_hom (inclusion hLM),
  le_refl := λ _, ⟨set.subset.refl _, by convert is_ring_hom.id; ext; simp⟩,
  le_trans := λ L M N ⟨hLM₁, hLM₂⟩ ⟨hMN₁, hMN₂⟩, ⟨set.subset.trans hLM₁ hMN₁,
    by resetI; convert is_ring_hom.comp (inclusion hLM₁) (inclusion hMN₁)⟩ }

-- def hom_of_le {L M : extension K} (h : L ≤ M) : L.carrier →ₐ[K] M.carrier :=
-- { to_fun := inclusion (classical.some h),
--   hom := (classical.some_spec h).1,
--   commutes' := (classical.some_spec h).2 }

private structure chain' (c : set (extension K)) : Prop :=
(chain : chain (≤) c)

local attribute [class] chain'

lemma is_chain (c : set (extension K)) [chain' c]: chain (≤) c :=
chain'.chain (by apply_instance)

section chain

variables (c : set (extension K)) [hcn : nonempty c]
include c  hcn

variable [hcn' : chain' c]
include hcn'

instance chain_directed_order : directed_preorder c :=
⟨λ ⟨i, hi⟩ ⟨j, hj⟩, let ⟨k, hkc, hk⟩ := chain.directed_on
  (is_chain c) i hi j hj in ⟨⟨k, hkc⟩, hk⟩⟩

def chain_map (i j : c) (hij : i ≤ j) : i.1.carrier → j.1.carrier :=
inclusion (exists.elim hij (λ h _, h))

instance chain_field_hom (i j : c) (hij : i ≤ j) : is_field_hom (chain_map c i j hij) :=
exists.elim hij (λ _, id)

instance chain_directed_system : directed_system (λ i : c, i.1.carrier) (chain_map c) :=
by split; intros; simp [chain_map]

def chain_limit : Type u := ring.direct_limit (λ i : c, i.1.carrier) (chain_map c)

lemma of_eq_of (x : big_type K) (i j : c) (hi : x ∈ i.1.carrier) (hj : x ∈ j.1.carrier) :
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) i ⟨x, hi⟩ =
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) j ⟨x, hj⟩ :=
have hij : i ≤ j ∨ j ≤ i,
  from show i.1 ≤ j.1 ∨ j.1 ≤ i.1, from chain.total (is_chain c) i.2 j.2,
hij.elim
  (λ hij, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
      _ _ _ hij,
    simp [chain_map, inclusion]
  end)
  (λ hij, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
      _ _ _ hij,
    simp [chain_map, inclusion]
  end)

lemma injective_aux (i j : c)
  (x y : ⋃ i : c, i.1.carrier) (hx : x.1 ∈ i.1.carrier) (hy : y.1 ∈ j.1.carrier) :
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) i ⟨x, hx⟩ =
  ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) j ⟨y, hy⟩ →
  x = y :=
have hij : i ≤ j ∨ j ≤ i,
  from show i.1 ≤ j.1 ∨ j.1 ≤ i.1, from chain.total (is_chain c) i.2 j.2,
have hinj : ∀ (i j : c) (hij : i ≤ j), injective (chain_map c i j hij),
  from λ _ _ _, is_field_hom.injective _,
hij.elim
  (λ hij h, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
      _ _ _ hij at h,
    simpa [chain_map, inclusion, subtype.coe_ext.symm] using ring.direct_limit.of_inj hinj j h,
  end)
  (λ hji h, begin
    rw ← @ring.direct_limit.of_f c _ _ _ (λ i : c, i.1.carrier) _ _ (chain_map c) _
      _ _ _ hji at h,
    simpa [chain_map, inclusion, subtype.coe_ext.symm] using ring.direct_limit.of_inj hinj i h,
  end)

def equiv_direct_limit : (⋃ (i : c), i.1.carrier) ≃
  ring.direct_limit (λ i : c, i.1.carrier) (chain_map c) :=
@equiv.of_bijective (⋃ i : c, i.1.carrier)
  (ring.direct_limit (λ i : c, i.1.carrier) (chain_map c))
  (λ x, ring.direct_limit.of _ _ (classical.some (set.mem_Union.1 x.2))
    ⟨_, classical.some_spec (set.mem_Union.1 x.2)⟩)
  ⟨λ x y, injective_aux _ _ _ _ _ _ _,
    λ x, let ⟨i, ⟨y, hy⟩, hy'⟩ := ring.direct_limit.exists_of x in
      ⟨⟨y, _, ⟨i, rfl⟩, hy⟩, begin
        convert hy',
        exact of_eq_of _ _ _ _ _ _
      end⟩⟩

instance Union_field : discrete_field (⋃ i : c, i.1.carrier) :=
@equiv.discrete_field _ _ (equiv_direct_limit c)
  (field.direct_limit.discrete_field _ _)

instance is_field_hom_Union (i : c) : is_field_hom
  (inclusion (set.subset_Union (λ i : c, i.1.carrier) i)) :=
suffices inclusion (set.subset_Union (λ i : c, i.1.carrier) i) =
    ((equiv_direct_limit c).symm ∘
    ring.direct_limit.of (λ i : c, i.1.carrier) (chain_map c) i),
  by rw this; exact is_ring_hom.comp _ _,
funext $ λ ⟨_, _⟩,
  (equiv_direct_limit c).injective $
    by rw [function.comp_app, equiv.apply_symm_apply];
      exact of_eq_of _ _ _ _ _ _

-- instance is_field_hom_range_Union [hc : nonempty c]
--   (h : set.range (bembedding K) ⊆ ⋃ i : c, i.1.carrier) :
--   is_field_hom (inclusion h) :=
-- let ⟨i⟩ := hc in
-- have h₁ : i.1.carrier ⊆ ⋃ i : c, i.1.carrier, from set.subset_Union _ i,
-- have h₂ : set.range (bembedding K) ⊆ i.1.carrier, from i.1.range_subset,
-- have inclusion h = inclusion h₁ ∘ inclusion h₂, by simp [function.comp],
-- by rw this; exact is_ring_hom.comp _ _

-- def chain_lift [nonempty c] (α : Type u) [discrete_field α] (i : set.range (bembedding K) → α)
--   [is_field_hom i] [is_algebraically_closed α] :
--   (⋃ i : c, i.1.carrier) → α :=
-- (ring.direct_limit.lift (λ j : c, j.1.carrier) (chain_map _ c) _
--   (λ j : c, j.1.lift i) (λ i j ⟨_, _, h⟩, by introsI; rw [h, chain_map])) ∘
--   (equiv_direct_limit K c)

-- def is_field_hom_chain_lift [nonempty c] (α : Type u) [discrete_field α]
--   (i : set.range (bembedding K) → α) [is_field_hom i]
--   [is_algebraically_closed α] : is_field_hom (chain_lift K c α i) :=
-- is_ring_hom.comp _ _

end chain

--def maximal_extension (c : set (extension K)) (hc : chain (≤) c) : extension K :=

def maximal_extension (c : set (extension K)) (hc : chain (≤) c) :
  { ub : extension K // ∀ L, L ∈ c → L ≤ ub } :=
if h : nonempty c
  then by letI : chain' c := ⟨hc⟩; exact
    ⟨{ carrier := ⋃ (i : c), i.1.carrier,
        /- The union is isomorphic to the direct limit. Suffices to prove the direct limit
          is an algebraic extension -/
        -- algebraic := sorry,
        algebra := sorry },
    λ e he, ⟨by convert subset_Union _ (⟨e, he⟩ : c); refl,
      is_field_hom_Union c ⟨e, he⟩⟩⟩
  else ⟨base_extension K, λ a ha, (h ⟨⟨a, ha⟩⟩).elim⟩

set_option old_structure_cmd true

structure algebraic_extension (K : Type u) [discrete_field K] extends extension K :=
(algebraic : ∀ x : carrier, is_integral K x)

open algebraic_extension

instance : preorder (algebraic_extension K) :=
preorder.lift algebraic_extension.to_extension (by apply_instance)

def maximal_algebraic_extension (c : set (algebraic_extension K)) (hc : chain (≤) c) :
  { ub : algebraic_extension K // ∀ L, L ∈ c → L ≤ ub } :=
let M := (maximal_extension (to_extension '' c) (chain.image (≤) _ _ (λ _ _, id) hc)) in
⟨{ algebraic := sorry, -- Field is isomorphic to direct limit of some algebraic extensions
    ..M.1 },
  λ L hL, M.2 _ (mem_image_of_mem _ hL)⟩

lemma exists_algebraic_closure (K : Type u) [discrete_field K] :
  ∃ m : algebraic_extension K, ∀ a, m ≤ a → a ≤ m :=
zorn (λ c hc, (maximal_algebraic_extension c hc).exists_of_subtype) (λ _ _ _, le_trans)

def closed_extension (K : Type u) [discrete_field K] :=
classical.some (exists_algebraic_closure K)

def algebraic_closure (K : Type u) [discrete_field K] : Type u :=
((classical.some (exists_algebraic_closure K))).carrier

end classical

namespace algebraic_closure

instance : discrete_field (algebraic_closure K) :=
{ has_decidable_eq := classical.dec_eq _,
  ..(classical.some (exists_algebraic_closure K)).field }

instance : algebra K (algebraic_closure K) :=
(classical.some (exists_algebraic_closure K)).algebra

def of : K → algebraic_closure K := algebra_map _

instance : is_ring_hom (@of K _) := by dunfold of; apply_instance

protected lemma is_integral (x : algebraic_closure K) : is_integral K x :=
(classical.some (exists_algebraic_closure K)).algebraic x

section lift
/- In this section, the homomorphism from any algebraic extension into an algebraic
  closure is proven to exist. -/
variables {L : Type v} {M : Type w} [discrete_field L] [algebra K L]
  [discrete_field M] [algebra K M] [is_algebraically_closed M] (hL : ∀ x : L, is_integral K x)

/-- This structure is used to prove the existence of a homomorphism from any algebraic extension
  into an algebraic closure -/
structure subfield_and_hom (K : Type u) (L : Type v) (M : Type w)
  [discrete_field K] [discrete_field L] [algebra K L] (hL : ∀ x : L, is_integral K x)
  [discrete_field M] [algebra K M] [is_algebraically_closed M] extends extension K :=
( to_algebraically_closed : carrier →ₐ[K] M )
( to_field : carrier → L )
( is_ring_hom_to_field : is_ring_hom to_field )

open subfield_and_hom

instance : preorder (subfield_and_hom K L M hL) :=
preorder.lift to_extension (by apply_instance)

def maximal_subfield_and_hom (c : set (subfield_and_hom K L M hL)) (hc : chain (≤) c) :
  { ub : subfield_and_hom K L M hL // ∀ N, N ∈ c → N ≤ ub } :=
let ub := (maximal_extension (to_extension '' c) (chain.image (≤) _ _ (λ _ _, id) hc)) in
⟨{ to_algebraically_closed := sorry, --field in question is direct limit of a bunch of fields with
      --algebra homs into M
    to_field := sorry, -- direct limit of a bunch of subfields is also a subfield
    is_ring_hom_to_field := sorry,
    ..ub.1 },
   λ n hN, ub.2 _ (mem_image_of_mem _ hN)⟩

end lift

section adjoin_root
variables {L : Type v} [discrete_field L] [algebra K L] (hL : ∀ x : L, is_integral K x)
  (f : polynomial L) [hif : irreducible f]
include hif

instance adjoin_root_algebraic_closure.field :
  discrete_field (adjoin_root f) := by apply_instance

instance adjoin_root_algebraic_closure.is_ring_hom :
  is_ring_hom (@adjoin_root.of _ _ _ f) := by apply_instance

def adjoin_root.of_embedding : L ↪ adjoin_root f :=
⟨adjoin_root.of, is_field_hom.injective _⟩

/-- TODO: move -/
instance adjoin_root.algebra : algebra K (adjoin_root f) :=
algebra.of_ring_hom (adjoin_root.of ∘ algebra_map _) (is_ring_hom.comp _ _)

def adjoin_root_extension_map : adjoin_root f ↪ big_type K :=
map (adjoin_root.of_embedding f) (algebraic_embedding_big_type hL)
  (λ i, let e : big_type K ↪ ℕ × polynomial K := i.trans
      (algebraic_embedding sorry) in --adjoining a root to an algebraic extension gives an algebraic extension
    cantor_injective e.1 e.2)

instance afhk : discrete_field (set.range (@adjoin_root_extension_map K _ _ _ _ hL f _)) :=
equiv.discrete_field (equiv.set.range _ (embedding.inj _)).symm

def adjoin_root_extension : extension K :=
{ carrier := set.range (@adjoin_root_extension_map K _ _ _ _ hL f _),
  algebra := algebra.of_ring_hom
    ((equiv.set.range _ (embedding.inj' (adjoin_root_extension_map hL f))).symm.symm ∘
      algebra_map _) (is_ring_hom.comp _ _) }


-- instance algebraic_closure_adjoin_root_comp.is_ring_hom :
--   is_ring_hom (@adjoin_root.of _ _ _ f ∘ of K) := is_ring_hom.comp _ _





-- lemma adjoin_root_extension_map_apply (x : algebraic_closure K) :
--   (adjoin_root_extension_map K f) (@adjoin_root.of _ _ _ f x) = x.val :=
-- map_commutes _ _ _ _

-- lemma closure_subset_adjoin_root :
--   (closed_extension K).carrier ⊆ set.range (adjoin_root_extension_map K f) :=
-- (λ x h, ⟨adjoin_root.of_embedding K f ⟨x, h⟩,
--   show (adjoin_root_extension_map K f)
--       (adjoin_root.of_embedding K f ⟨x, h⟩) =
--       (⟨x, h⟩ : algebraic_closure K).val,
--     from map_commutes _ _ _ _⟩)

-- lemma adjoin_root_range_subset :
--   (set.range (bembedding K)) ⊆ set.range (adjoin_root_extension_map K f) :=
-- set.subset.trans
--   (classical.some (exists_algebraic_closure K)).range_subset
--   (closure_subset_adjoin_root K f)

-- lemma adjoin_root_inclusion_eq :
--   inclusion (adjoin_root_range_subset K f) =
--   (equiv.set.range _ (adjoin_root_extension_map K f).2) ∘
--   (@adjoin_root.of (algebraic_closure K) _ _ f) ∘
--   inclusion (classical.some (exists_algebraic_closure K)).range_subset :=
-- funext $ λ x, subtype.eq $
--   by simp [inclusion, function.comp, adjoin_root_extension_map_apply]

-- lemma adjoin_root_inclusion_eq' :
--   inclusion (closure_subset_adjoin_root K f) =
--   (equiv.set.range _ (adjoin_root_extension_map K f).2) ∘
--   (@adjoin_root.of (algebraic_closure K) _ _ f) :=
-- funext $ λ x, subtype.eq $
--   by simp [inclusion, function.comp, adjoin_root_extension_map_apply]; refl

-- instance adjoin_root_range.discrete_field :
--   discrete_field (set.range (adjoin_root_extension_map K f)) :=
-- equiv.discrete_field (equiv.set.range _ (embedding.inj _)).symm

-- instance adjoin_root_inclusion.is_ring_hom :
--   is_ring_hom (inclusion (adjoin_root_range_subset K f)) :=
-- begin
--   letI := (classical.some (exists_algebraic_closure K)).is_field_hom,
--   rw [adjoin_root_inclusion_eq, ← equiv.symm_symm (equiv.set.range _ _)],
--   exact @is_ring_hom.comp _ _ _ _ _ (is_ring_hom.comp _ _) _ _ _
--     (equiv.is_ring_hom.symm _)
-- end
-- --set_option eqn_compiler.zeta true

-- def adjoin_root_lift {α : Type u} [_inst_2_1 : discrete_field α] (i : (range ⇑(bembedding K)) → α)
--   [is_field_hom i] [is_algebraically_closed α] :
--   (range ⇑(adjoin_root_extension_map K f)) → α :=
-- begin
--   have h : _ := is_algebraically_closed.exists_root
--     (f.map (lift_aux K i))
--     (by rw degree_map; exact degree_pos_of_ne_zero_of_nonunit
--       (ne_zero_of_irreducible hif) hif.1),
--   exact adjoin_root.lift (lift_aux K i) (classical.some h) (by rw [← eval_map];
--     exact (classical.some_spec h)) ∘
--   (equiv.set.range _ (adjoin_root_extension_map K f).2).symm
-- end

-- lemma adjoin_root_lift.is_ring_hom {α : Type u} [_inst_2_1 : discrete_field α]
--   (i : (range ⇑(bembedding K)) → α) [is_field_hom i] [is_algebraically_closed α] :
--   is_field_hom (adjoin_root_lift _ f i) :=
-- begin
--   letI := equiv.is_ring_hom.symm (equiv.set.range _ (adjoin_root_extension_map K f).2),
--   dsimp [adjoin_root_lift],
--   rw [← equiv.symm_symm (equiv.set.range _ _)],
--   exact is_ring_hom.comp _ _
-- end


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
