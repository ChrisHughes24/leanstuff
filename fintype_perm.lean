import data.multiset data.equiv.basic data.nat.basic group_theory.perm

open equiv.perm equiv list

variables {α : Type*} {β : Type*} [decidable_eq α]

def thing : list α → list (perm α)
| []       := [1]
| (a :: l) := thing l ++ l.bind (λ b, (thing l).map (λ f, swap a b * f))

@[simp] lemma thing_nil : thing ([] : list α) = [1] := rfl

lemma length_thing : ∀ l : list α, length (thing l) = l.length.fact
| []       := rfl
| (a :: l) := by rw [length_cons, nat.fact_succ];
  simp [thing, length_bind, length_thing, function.comp, nat.succ_mul]

lemma mem_thing : ∀ (l : list α) (f : perm α) (hl : l.nodup) (h : ∀ x, f x ≠ x → x ∈ l), f ∈ thing l
| []     f hl h := list.mem_singleton.2 $ equiv.ext _ _$ λ x, by simp [imp_false, *] at *
| (a::l) f hl h :=
if hfa : f a = a
then
  mem_append_left _ $ mem_thing _ _ (list.nodup_of_nodup_cons hl)
    (λ x hx, mem_of_ne_of_mem (λ h, by rw h at hx; exact hx hfa) (h x hx))
else
have hfa' : f (f a) ≠ f a, from mt (λ h, f.bijective.1 h) hfa,
have ∀ (x : α), (swap a (f a) * f) x ≠ x → x ∈ l,
  from λ x hx, have hxa : x ≠ a, from λ h, by simpa [h, mul_apply] using hx,
    have hfxa : f x ≠ f a, from mt (λ h, f.bijective.1 h) hxa,
    list.mem_of_ne_of_mem hxa
      (h x (λ h, by simp [h, mul_apply, swap_apply_def] at hx; split_ifs at hx; cc)),
suffices f ∈ thing l ∨ ∃ (b : α), b ∈ l ∧ ∃ g : perm α, g ∈ thing l ∧ swap a b * g = f,
  by simpa [thing],
(@or_iff_not_imp_left _ _ (classical.prop_decidable _)).2
  (λ hfl, ⟨f a,
    if hffa : f (f a) = a then mem_of_ne_of_mem hfa (h _ (mt (λ h, f.bijective.1 h) hfa))
      else this _ $ by simp [mul_apply, swap_apply_def]; split_ifs; cc,
    ⟨swap a (f a) * f, mem_thing _ _ (list.nodup_of_nodup_cons hl) this,
      by rw [← mul_assoc, mul_def (swap a (f a)) (swap a (f a)), swap_swap, ← one_def, one_mul]⟩⟩)

lemma mem_thing' : ∀ (l : list α) (f : perm α), f ∈ thing l → ∀ x, f x ≠ x → x ∈ l
| []     f h := have f = 1 := by simpa [thing] using h, by rw this; simp
| (a::l) f h :=
(mem_append.1 h).elim
  (λ h x hx, mem_cons_of_mem _ (mem_thing' l f h x hx))
  (λ h x hx,
    let ⟨y, hy, hy'⟩ := mem_bind.1 h in
    let ⟨g, hg₁, hg₂⟩ := mem_map.1 hy' in
    if hxa : x = a then by simp [hxa]
    else if hxy : x = y then mem_cons_of_mem _ $ by rwa hxy
    else mem_cons_of_mem _ $
    mem_thing' l g hg₁ _ $
      by rw [eq_inv_mul_iff_mul_eq.2 hg₂, mul_apply, swap_inv, swap_apply_def];
        split_ifs; cc)

lemma nodup_thing : ∀ (l : list α) (hl : l.nodup), (thing l).nodup
| []     hl := by simp [thing]
| (a::l) hl :=
have hl' : l.nodup, from nodup_of_nodup_cons hl,
have hln' : (thing l).nodup, from nodup_thing _ hl',
have hmeml : ∀ {f : perm α}, f ∈ thing l → f a = a,
  from λ f hf, not_not.1 (mt (mem_thing' l f hf a) (nodup_cons.1 hl).1),
by rw [thing, list.nodup_append, list.nodup_bind, pairwise_iff_nth_le]; exact
⟨hln', ⟨λ _ _, nodup_map (λ _ _, (mul_left_inj _).1) hln',
  λ i j hj hij x hx₁ hx₂,
    let ⟨f, hf⟩ := mem_map.1 hx₁ in
    let ⟨g, hg⟩ := mem_map.1 hx₂ in
    have hix : x a = nth_le l i (lt_trans hij hj),
      by rw [← hf.2, mul_apply, hmeml hf.1, swap_apply_left],
    have hiy : x a = nth_le l j hj,
      by rw [← hg.2, mul_apply, hmeml hg.1, swap_apply_left],
    absurd (hf.2.trans (hg.2.symm)) $
      λ h, ne_of_lt hij $ nodup_iff_nth_le_inj.1 hl' i j (lt_trans hij hj) hj $
        by rw [← hix, hiy]⟩,
  λ f hf₁ hf₂,
    let ⟨x, hx, hx'⟩ := mem_bind.1 hf₂ in
    let ⟨g, hg⟩ := mem_map.1 hx' in
    have hgxa : g⁻¹ x = a, from f.bijective.1 $
      by rw [hmeml hf₁, ← hg.2]; simp,
    have hxa : x ≠ a, from λ h, (list.nodup_cons.1 hl).1 (h ▸ hx),
    (list.nodup_cons.1 hl).1 $
      hgxa ▸ mem_thing' _ _ hg.1 _ (by rwa [apply_inv_self, hgxa])⟩

def perm_fintype_aux [decidable_eq (perm α)] {s : multiset α} :
  (∀ x, x ∈ s) → s.nodup → fintype (perm α) :=
quotient.rec_on_subsingleton s (λ l hl hln, ⟨⟨thing l, nodup_thing _ hln⟩,
  (λ x, mem_thing _ _ hln (λ _ _, (hl _)))⟩)

instance perm.fintype [fintype α] : fintype (perm α) := perm_fintype_aux finset.mem_univ finset.univ.2

lemma card_perm [fintype α] : fintype.card (perm α) = (fintype.card α).fact :=
quotient.induction_on (@finset.univ α _).1 begin end

#exit

lemma thing_cons (m : multiset α) (a : α) :
  thing (a :: m) = thing m + m.bind (λ b, (thing m).map (λ f, swap a b * f)) :=
by simp [thing]

lemma mem_perm (m : multiset α) (f : perm α) : (∀ x, f x ≠ x → x ∈ m) → f ∈ thing m :=
multiset.induction_on m
  (λ h, mem_singleton.2 $ equiv.ext _ _ $ λ x, not_not.1 $ by simpa [-not_not, not_mem_zero] using h x)
  $ λ a s ih h, begin
    simp [thing_cons],

  end

lemma card_perm (m : multiset α) : (thing m).card = nat.fact m.card :=
multiset.induction_on m rfl (λ a s ih, by rw [card_cons, nat.fact_succ];
  simp [thing_cons, card_add, ih, card_bind, mul_comm, nat.mul_succ])

def perm.cons (e : α ≃ β) (m : multiset α) (a : α) (b : β) (f : α ≃ β) : α ≃ β :=
(swap a (e.symm b)).trans f

def list_to_function : Π (l₁ : list α) (l₂ : list β), l₁.length = l₂.length → Π a ∈ l₁, β
| []      l₂      h₁ a h₂ := absurd h₂ (list.not_mem_nil _)
| (b::l₁) []      h₁ a h₂ := absurd h₁ (nat.succ_ne_zero _)
| (b::l₁) (c::l₂) h₁ a h₂ := if h : a = b then c
  else list_to_function l₁ l₂ (nat.succ_inj h₁) a (list.mem_of_ne_of_mem h h₂)

open list nat

def list_to_perm : Π (l₁ : list α) (l₂ : list β), l₁.length = l₂.length →
  {a // a ∈ l₁} ≃ {b // b ∈ l₂}
| []      []      h := ⟨λ a, (not_mem_nil _ a.2).elim, λ b, (not_mem_nil _ b.2).elim,
  λ a, (not_mem_nil _ a.2).elim, λ b, (not_mem_nil _ b.2).elim⟩
| []      (b::l₂) h := (succ_ne_zero _ h.symm).elim
| (a::l₁) []      h := (succ_ne_zero _ h).elim
| (a::l₁) (b::l₂) h :=
let f := list_to_perm l₁ l₂ (succ_inj h) in
{ to_fun := λ x, if h : x.1 = a then ⟨b, list.mem_cons_self _ _⟩
            else ⟨(f ⟨x, mem_of_ne_of_mem h x.2⟩).1, mem_cons_of_mem _ begin end⟩  }

def multiset.perm (m : multiset α) (t : multiset β) : multiset (α ≃ β) :=
multiset.rec_on m (e :: 0)
  (λ a m ih, m.bind (λ b, ih.map (λ f, begin end)))
  (λ x y s t, heq_of_eq begin
    simp [multiset.map_bind, bind_bind, swap_comm],
    rw [bind_map_comm],

  end)