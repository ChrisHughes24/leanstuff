import ring_theory.adjoin_root tactic.tidy order.zorn data.equiv.algebra

universes u v
open polynomial zorn
variables (K : Type u) [discrete_field K]

inductive big_type_aux : Type u
| of_field : K → big_type_aux
| root : ℕ → (ℕ → big_type_aux) → big_type_aux

def big_type := set (big_type_aux K)

def inclusion {α : Type*} {s t : set α} (h : s ⊆ t) : s → t :=
λ x : s, (⟨x, h x.2⟩ : t)

instance : preorder (Σ s : set (big_type K), discrete_field s) :=
{ le := λ s t, ∃ hst : s.1 ⊆ t.1,
    by haveI := s.2; haveI := t.2; exact is_field_hom (inclusion hst),
  le_refl := λ ⟨_, _⟩, ⟨set.subset.refl _, by simpa [inclusion] using is_ring_hom.id⟩,
  le_trans := λ ⟨s, Is⟩ ⟨t, It⟩ ⟨u, Iu⟩ ⟨hst, hst'⟩ ⟨htu, htu'⟩,
    ⟨set.subset.trans hst htu,
      by resetI; convert @is_ring_hom.comp s t _ _ _ hst' u _ _ htu'⟩ }

-- lemma discrete_field.ext {α : Type*} (a b : discrete_field α)
--   (h : @is_field_hom α α (by haveI := a; apply_instance) (by haveI := b; apply_instance) id) :
--   a = b :=
-- begin
--   have h₁ := @is_ring_hom.map_add  α α (id _) (id _) id h,
--   have h₂ := @is_ring_hom.map_zero α α (id _) (id _) id h,
--   have h₃ := @is_ring_hom.map_neg  α α (id _) (id _) id h,
--   have h₄ := @is_ring_hom.map_mul  α α (id _) (id _) id h,
--   have h₅ := @is_ring_hom.map_one  α α (id _) (id _) id h,
--   have h₆ := @is_field_hom.map_inv α α (id _) (id _) id h,
--   resetI, cases a, cases b,
--   congr; funext,
--   exact h₁, exact h₂, exact h₃, exact h₄, exact h₅, exact h₆
-- end

inductive in_algebraic_closure {L : Type v} [discrete_field L] (i : K → L) : L → Prop
| of_field : ∀ x, in_algebraic_closure (i x)
| root     : ∀ (l : L) (f : polynomial L), f ≠ 0 → (∀ n : ℕ, in_algebraic_closure (f.coeff n)) →
  is_root f l → in_algebraic_closure l

local attribute [instance, priority 0] classical.dec

noncomputable def big_type_aux_map {L : Type*} [discrete_field L] (i : K → L) [is_field_hom i]
  (h : ∀ l : L, in_algebraic_closure K i l) (x : big_type_aux K) : L :=
big_type_aux.rec_on x i
  (λ n f poly, if h : ∃ j : polynomial L, (∀ m, j.coeff m = poly m) ∧ n < j.roots.card
    then list.nth_le (quotient.out (classical.some h).roots.1) n begin
      show n < multiset.card (quotient.mk _),
      rw [quotient.out_eq], exact (classical.some_spec h).2
    end
    else 0)

lemma surjective_big_type_aux_map {L : Type*} [discrete_field L] (i : K → L) [is_field_hom i]
  (h : ∀ l : L, in_algebraic_closure K i l) : function.surjective (big_type_aux_map K i h) :=
λ l, in_algebraic_closure.rec_on (h l)
  (λ k, ⟨big_type_aux.of_field k, rfl⟩)
  (λ l f hf0 _ hfl ih,
    let ⟨g, hg⟩ := classical.axiom_of_choice ih in
    have ∃ j : polynomial L, (∀ m, j.coeff m = big_type_aux_map K i h (g m)) ∧
        (quotient.out (f.roots).1).index_of l < j.roots.card,
      from ⟨f, λ _, (hg _).symm,
        calc _ < multiset.card ⟦(quotient.out f.roots.1)⟧ : list.index_of_lt_length.2
          (show l ∈ (show multiset _, from quotient.mk (quotient.out f.roots.1)),
            by simp only [quotient.out_eq]; exact (mem_roots hf0).2 hfl)
        ... = _ : by rw quotient.out_eq; refl⟩,
    have hfthis : f = classical.some this,
      from polynomial.ext.2 (λ m, by rw [(classical.some_spec this).1 m, hg]),
    ⟨big_type_aux.root (list.index_of l (quotient.out (f.roots).1)) g,
      begin
        dsimp [big_type_aux_map],
        erw dif_pos this,
        simp [hfthis.symm]
      end⟩)

def embedding : K ↪ big_type K :=
⟨λ x, ({big_type_aux.of_field x} : set (big_type_aux K)), λ _ _, by simp⟩

noncomputable instance : discrete_field (set.range (embedding K)) :=
equiv.discrete_field (show K ≃ set.range (embedding K),
  from equiv.of_bijective
    (show function.bijective (λ k : K, (⟨embedding K k, k, rfl⟩ : set.range (embedding K))),
      from ⟨λ x y hxy, (embedding K).2 (subtype.mk.inj hxy),
        λ ⟨_, k, hk⟩, ⟨k, subtype.eq hk⟩⟩)).symm

def extensions : Type u :=
{s : Σ s : set (big_type K), discrete_field s //
  ∃ h : set.range (embedding K) ⊆ s.1,
  by letI := s.2; exact is_field_hom (inclusion h) ∧
    ∀ x : s.1, in_algebraic_closure _ (inclusion h) x}

instance extensions.field (L : extensions K) :
  discrete_field L.1.1 := L.1.2

instance : has_coe (extensions K) (Σ s : set (big_type K), discrete_field s) :=
⟨subtype.val⟩

lemma exists_max_of_chain {c : set (extensions K)}
  (hc : chain (λ (m a : extensions K), m.1 ≤ a.1) c)
  (x y : ↥⋃ (s : c), s.1.1.1) :
  ∃ L : extensions K, L ∈ c ∧
  ↑x ∈ (L : Σ s : set (big_type K), discrete_field s).1 ∧
  ↑y ∈ (L : Σ s : set (big_type K), discrete_field s).1 :=
let ⟨u, ⟨sx, hsx⟩, hu⟩ := x.2 in
let ⟨v, ⟨sy, hsy⟩, hv⟩ := y.2 in
by simp only [hsx.symm, hsy.symm] at *; exact
((@or_iff_not_imp_left _ _ (classical.dec _)).2 (hc sx sx.2 sy sy.2)).elim
  (λ h, ⟨sx, sx.2, hu, h.symm ▸ hv⟩)
  (λ h, h.elim
    (λ ⟨h₁, h₂⟩, by exact ⟨sy, sy.2, h₁ hu, hv⟩)
    (λ ⟨h₁, h₂⟩, ⟨sx, sx.2, hu, h₁ hv⟩))

noncomputable def max_of_chain {c : set (extensions K)}
  (hc : chain (λ (m a : extensions K), m.1 ≤ a.1) c)
  (x y : ↥⋃ (s : c), s.1.1.1) : extensions K :=
classical.some (exists_max_of_chain K hc x y)

lemma mem_max_of_chain {c : set (extensions K)}
  (hc : chain (λ (m a : extensions K), m.1 ≤ a.1) c)
  (x y : ↥⋃ (s : c), s.1.1.1) :
  ↑x ∈ (↑(max_of_chain K hc x y) : Σ s : set (big_type K), discrete_field s).1 ∧
  ↑y ∈ (↑(max_of_chain K hc x y) : Σ s : set (big_type K), discrete_field s).1 :=
(classical.some_spec (exists_max_of_chain K hc x y)).2

lemma max_of_chain_mem {c : set (extensions K)}
  (hc : chain (λ (m a : extensions K), m.1 ≤ a.1) c)
  (x y : ↥⋃ (s : c), s.1.1.1) : max_of_chain K hc x y ∈ c :=
(classical.some_spec (exists_max_of_chain K hc x y)).1

noncomputable def lift_bin {c : set (extensions K)}
  (hc : chain (λ (m a : extensions K), m.1 ≤ a) c)
  (bin : Π s : extensions K, s.1.1 → s.1.1 → s.1.1)
  (x y : ↥⋃ (s : c), s.1.1.1) : ↥⋃ (s : c), s.1.1.1 :=
let z := (bin (max_of_chain K hc x y)
    ⟨x, (mem_max_of_chain K hc x y).1⟩ ⟨y, (mem_max_of_chain K hc x y).2⟩) in
inclusion (λ z hz, ⟨_, ⟨⟨_, max_of_chain_mem K hc x y⟩, rfl⟩, hz⟩) z

lemma lift_add_assoc {c : set (extensions K)}
  (hc : chain (λ (m a : extensions K), m.1 ≤ a) c)
  (x y z : ↥⋃ (s : c), s.1.1.1) :
lift_bin K hc (λ _, (+)) (lift_bin K hc (λ _, (+)) x y) z =
lift_bin K hc (λ _, (+)) x (lift_bin K hc (λ _, (+)) y z) :=
begin
  simp [lift_bin, -add_comm],

end

example (c : set (extensions K))
  (hc : chain (λ (m a : extensions K), m.1 ≤ a) c)
  (x : c) : discrete_field (↥⋃ (x : c), x.1.1.1) :=
{ zero := ⟨↑(0 : set.range (embedding K)), x.1.1.1, ⟨x, rfl⟩,
    let ⟨h, _⟩ := x.1.2 in h (subtype.property (0 : set.range (embedding K)))⟩,
  one := ⟨↑(1 : set.range (embedding K)), x.1.1.1, ⟨x, rfl⟩,
    let ⟨h, _⟩ := x.1.2 in h (subtype.property (1 : set.range (embedding K)))⟩,
  add := λ x y, begin



  end }
#print imax
#print chain

def algebraic_closure_aux : ∃ m : set_thinger K, ∀ a, m ≤ a → a ≤ m :=
zorn
  (λ c hc, if h : c = ∅
    then ⟨⟨⟨set.range (thing1er K), infer_instance⟩,
      ⟨by refl, by simp [inclusion, subtype.eta]; exact is_ring_hom.id⟩⟩,
        λ a ha, absurd ha (h.symm ▸ set.not_mem_empty _)⟩
    else ⟨⟨⟨⋃ x : c, x.1.1.1, _⟩, _⟩, sorry⟩)
  (λ _ _ _, le_trans)




-- noncomputable def field_of_equiv {α β : Type*} [discrete_field α] (e : α ≃ β) : discrete_field β :=
-- { zero := e 0,
--   one  := e 1,
--   add := λ x y, e (e.symm x + e.symm y),
--   mul := λ x y, e (e.symm x * e.symm y),
--   neg := λ x, e (-e.symm x),
--   inv := λ x, e (e.symm x)⁻¹,
--   left_distrib := by simp; intros; apply left_distrib,
--   add_assoc := by simp; intros; apply add_assoc,
--   mul_one := λ _, by apply congr_arg e; exact _,
--   zero_add := by simp; intros; convert zero_add _,
--   add_zero := by simp; intros; convert add_zero _,
--   add_left_neg := by simp; intros; convert add_left_neg _ _,
--   add_comm := by simp; intros; convert add_comm _ _,
--   mul_assoc := by simp; intros; convert mul_assoc _ _ _,
--   one_mul := by simp; intros; convert one_mul _,
--   right_distrib := by simp; intros; convert right_distrib _ _ _,
--   zero_ne_one := by simp; intros; convert zero_ne_one,
--   mul_inv_cancel := by simp; intros; convert mul_inv_cancel _ _,
--   inv_mul_cancel := by simp; intros; convert inv_mul_cancel _ _,
--   mul_comm := by simp; intros; convert mul_comm _ _,
--   has_decidable_eq := classical.dec_eq _,
--   inv_zero := by simp; intros; convert inv_zero }
