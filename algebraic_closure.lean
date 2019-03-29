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
equiv.discrete_field (equiv.set.range _ (embedding K).2).symm

def extensions : Type u :=
{s : Σ s : set (big_type K), discrete_field s //
  ∃ h : set.range (embedding K) ⊆ s.1,
  by letI := s.2; exact is_field_hom (inclusion h) ∧
    ∀ x : s.1, in_algebraic_closure _ (inclusion h) x}

instance extensions.field (L : extensions K) :
  discrete_field L.1.1 := L.1.2

instance : has_coe (extensions K) (Σ s : set (big_type K), discrete_field s) :=
⟨subtype.val⟩

instance : preorder (extensions K) :=
{ le := λ x y, x.1 ≤ y.1,
  le_refl := λ _, le_refl _,
  le_trans := λ _ _ _, le_trans }

def algebraic_closure_aux : ∃ m : extensions K, ∀ a, m ≤ a → a ≤ m :=
zorn
  (λ c hc, if h : c = ∅
    then ⟨⟨⟨set.range (embedding K), by apply_instance⟩,
        by refl, by split; intros; apply subtype.eq; simp [inclusion],
        λ ⟨x, _⟩, by simp [inclusion];
          exact in_algebraic_closure.of_field id _⟩,
      λ a, h.symm ▸ false.elim⟩
    else _)
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
