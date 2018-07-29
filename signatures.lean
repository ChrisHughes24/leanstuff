import data.fintype

open equiv function finset 
variables {α : Type*} {β : Type*}

instance decidable_eq_equiv [decidable_eq α] [decidable_eq β] 
  [fintype α] : decidable_eq (α ≃ β) :=
λ a b, decidable_of_iff (a.1 = b.1)
  ⟨λ h, equiv.ext _ _ (congr_fun h), congr_arg _⟩

instance {n : ℕ} : decidable_linear_order (fin n) :=
{ decidable_le := fin.decidable_le,
  ..fin.linear_order }

def trunc_decidable_linear_order_fintype (α : Type*) [decidable_eq α] [fintype α] :
  trunc (decidable_linear_order α) :=
trunc.rec_on_subsingleton (fintype.equiv_fin α)
(λ f, trunc.mk 
  { le := λ a b, f a ≤ f b,
    lt := λ a b, f a < f b,
    le_refl := λ a, le_refl (f a),
    le_trans := λ a b c, @le_trans _ _ (f a) _ _,
    le_antisymm := λ a b h₁ h₂, f.bijective.1 (le_antisymm h₁ h₂),
    le_total := λ a b, le_total (f a) _,
    lt_iff_le_not_le := λ a b, @lt_iff_le_not_le _ _ (f a) _,
    decidable_le := λ a b, fin.decidable_le _ _ })

namespace finset

def attach_fin (s : finset ℕ) {n : ℕ} (h : ∀ m ∈ s, m < n) :
  finset (fin n) := 
⟨s.1.pmap (λ a ha, ⟨a, ha⟩) h, multiset.nodup_pmap (λ _ _ _ _, fin.mk.inj) s.2⟩

@[simp] lemma mem_attach_fin {n : ℕ} {s : finset ℕ} (h : ∀ m ∈ s, m < n) {a : fin n} :
  a ∈ s.attach_fin h ↔ a.1 ∈ s :=
⟨λ h, let ⟨b, hb₁, hb₂⟩ := multiset.mem_pmap.1 h in hb₂ ▸ hb₁, 
λ h, multiset.mem_pmap.2 ⟨a.1, h, fin.eta _ _⟩⟩

@[simp] lemma eq_empty_iff_forall_not_mem {s : finset α} : s = ∅ ↔ ∀ x, x ∉ s :=
⟨λ h, by simp [h], λ h, eq_empty_of_forall_not_mem h⟩

end finset

@[derive decidable_eq] inductive mu2
|     one : mu2
| neg_one : mu2

namespace mu2

def neg : mu2 → mu2
|     one := neg_one
| neg_one :=     one

instance : has_one mu2 := ⟨one⟩
instance : has_neg mu2 := ⟨neg⟩
instance : fintype mu2 := ⟨{one, neg_one}, λ a, by cases a; simp⟩

@[simp] lemma card_mu2 : fintype.card mu2 = 2 := rfl

def mul : mu2 → mu2 → mu2
|   1    1  :=  1
| (-1) (-1) :=  1
|   1  (-1) := -1
| (-1)   1  := -1

instance : has_mul mu2 := ⟨mul⟩

instance : comm_group mu2 :=
by refine_struct { mul := mul, inv := id, one := 1 }; exact dec_trivial

end mu2

namespace equiv.perm

@[simp] lemma one_apply (a : α) : 
  (1 : perm α) a = a := rfl

@[simp] lemma mul_apply (f g : perm α) (a : α) : 
  (f * g) a = f (g a) := rfl

@[simp] lemma inv_apply_self (f : perm α) (a : α) : 
  f⁻¹ (f a) = a := equiv.inverse_apply_apply _ _

@[simp] lemma apply_inv_self (f : perm α) (a : α) : 
  f (f⁻¹ a) = a := equiv.apply_inverse_apply _ _

lemma one_def : (1 : perm α) = equiv.refl α := rfl

lemma mul_def (f g : perm α) : f * g = g.trans f := rfl

lemma inv_def (f : perm α) : f⁻¹ = f.symm := rfl

def transpose [decidable_eq α] (x y : α) : perm α :=
{ to_fun := λ a, if a = x then y else if a = y then x else a,
  inv_fun := λ a, if a = x then y else if a = y then x else a,
  left_inv := λ a, by dsimp; split_ifs; cc,
  right_inv := λ a, by dsimp; split_ifs; cc }

@[simp] lemma transpose_left [decidable_eq α] (x y : α) :
   transpose x y x = y :=
by rw transpose; simp [if_pos rfl]

@[simp] lemma transpose_right [decidable_eq α] (x y : α) :
   transpose x y y = x :=
by rw transpose; dsimp; split_ifs; simp *

@[simp] lemma transpose_self [decidable_eq α] (x : α) :
  transpose x x = 1 := 
equiv.ext _ _ $ λ a, by dsimp [transpose]; split_ifs; cc

lemma transpose_eq_of_ne [decidable_eq α] {x y a : α} (hx : a ≠ x)
  (hy : a ≠ y) : transpose x y a = a :=
by rw transpose; simp [if_neg hx, if_neg hy]

lemma transpose_comm [decidable_eq α] (x y : α) :
  transpose x y = transpose y x :=
equiv.ext _ _ $ λ a, by dsimp [transpose]; split_ifs; cc

@[simp] lemma transpose_inv [decidable_eq α] (x y : α) :
  (transpose x y)⁻¹ = transpose x y := rfl

lemma transpose_apply [decidable_eq α] (x y a : α) :
  transpose x y a = if a = x then y else if a = y then x else a := rfl

lemma ite_apply {p : Prop} [decidable p] (f g : perm α) (x : α) : 
  (if p then f else g).1 x = if p then f.1 x else g.1 x :=
if h : p then by rw [if_pos h, if_pos h]; refl else by rw [if_neg h, if_neg h]; refl

lemma ite_inv_apply {p : Prop} [decidable p] (f g : perm α) (x : α) : 
  (if p then f else g).2 x = if p then f.2 x else g.2 x :=
if h : p then by rw [if_pos h, if_pos h]; refl else by rw [if_neg h, if_neg h]; refl

lemma transpose_conj [decidable_eq α] {a b x y : α} 
  (hab : a ≠ b) (hxy : x ≠ y) :
  {f : perm α // f * transpose x y * f⁻¹ = transpose a b} :=
⟨if x = b then transpose y a 
else if y = a then transpose x b
else transpose x a * transpose y b, equiv.ext _ _ $ λ n,
begin
  unfold_coes,
  dsimp [transpose, inv_def, mul_def, equiv.symm, equiv.trans, function.comp, equiv.to_fun],
  simp only [ite_apply, ite_inv_apply],
  split_ifs; cc
end⟩

/-- set of all pairs ⟨a, b⟩ : Σ a : fin n, fin n such that b < a -/
def fin_pairs_lt (n : ℕ) : finset (Σ a : fin n, fin n) :=
(univ : finset (fin n)).sigma (λ a, (range a.1).attach_fin
  (λ m hm, lt_trans (mem_range.1 hm) a.2))

def sign_aux {n : ℕ} (a : perm (fin n)) : mu2 :=
(fin_pairs_lt n).prod
(λ x, if a x.1 ≤ a x.2 then -1 else 1)

lemma mem_fin_pairs_lt {n : ℕ} {a : Σ a : fin n, fin n} : 
  a ∈ fin_pairs_lt n ↔ a.2 < a.1 :=
by simp [fin_pairs_lt, fin.lt_def]

@[simp] lemma sign_aux_one (n : ℕ) : sign_aux (1 : perm (fin n)) = 1 :=
begin
  unfold sign_aux,
  conv { to_rhs, rw ← @finset.prod_const_one _ mu2
    (fin_pairs_lt n) },
  exact finset.prod_congr rfl (λ a ha, if_neg 
    (not_le_of_gt (mem_fin_pairs_lt.1 ha)))
end

@[simp] lemma equiv.symm.trans_apply {α β γ : Type*} (f : α ≃ β) (g : β ≃ γ) (a : γ) : 
  (f.trans g).symm a = f.symm (g.symm a) := rfl

def sign_bij_aux {n : ℕ} (f : perm (fin n)) (a : Σ a : fin n, fin n) :
  Σ a : fin n, fin n :=
if hxa : f a.2 < f a.1
then ⟨f a.1, f a.2⟩
else ⟨f a.2, f a.1⟩

lemma sign_bij_aux_inj {n : ℕ} {f : perm (fin n)} : ∀ a b : Σ a : fin n, fin n,
   a ∈ fin_pairs_lt n → b ∈ fin_pairs_lt n → sign_bij_aux f a = sign_bij_aux f b → a = b :=
λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h, begin
  unfold sign_bij_aux at h,
  rw mem_fin_pairs_lt at *,
  have : ¬b₁ < b₂ := not_lt_of_ge (le_of_lt hb),
  split_ifs at h;
  simp [*, injective.eq_iff f.bijective.1, sigma.mk.inj_eq] at *
end

lemma sign_bij_aux_surj {n : ℕ} {f : perm (fin n)} : ∀ a ∈ fin_pairs_lt n,
  ∃ b ∈ fin_pairs_lt n, a = sign_bij_aux f b :=
λ ⟨a₁, a₂⟩ ha,
if hxa : f⁻¹ a₂ < f⁻¹ a₁
then ⟨⟨f⁻¹ a₁, f⁻¹ a₂⟩, mem_fin_pairs_lt.2 hxa,
  by dsimp [sign_bij_aux];
    rw [apply_inv_self, apply_inv_self, dif_pos (mem_fin_pairs_lt.1 ha)]⟩
else ⟨⟨f⁻¹ a₂, f⁻¹ a₁⟩, mem_fin_pairs_lt.2 $ lt_of_le_of_ne
  (le_of_not_gt hxa) $ λ h,
    by simpa [mem_fin_pairs_lt, (f⁻¹).bijective.1 h, lt_irrefl] using ha,
  by dsimp [sign_bij_aux];
    rw [apply_inv_self, apply_inv_self, 
      dif_neg (not_lt_of_ge (le_of_lt (mem_fin_pairs_lt.1 ha)))]⟩

lemma sign_bij_aux_mem {n : ℕ} {f : perm (fin n)}: ∀ a : Σ a : fin n, fin n,
  a ∈ fin_pairs_lt n → sign_bij_aux f a ∈ fin_pairs_lt n :=
λ ⟨a₁, a₂⟩ ha, begin
  unfold sign_bij_aux,
  split_ifs with h,
  { exact mem_fin_pairs_lt.2 h },
  { exact mem_fin_pairs_lt.2
    (lt_of_le_of_ne (le_of_not_gt h)
      (λ h, ne_of_lt (mem_fin_pairs_lt.1 ha) (f.bijective.1 h.symm))) }
end

@[simp] lemma sign_aux_inv {n : ℕ} (f : perm (fin n)) : sign_aux f⁻¹ = sign_aux f :=
prod_bij (λ a ha, sign_bij_aux f⁻¹ a)
sign_bij_aux_mem
(λ ⟨a, b⟩ hab, if h : f⁻¹ b < f⁻¹ a
  then by rw [sign_bij_aux, dif_pos h, if_neg (not_le_of_gt h), apply_inv_self,
    apply_inv_self, if_neg (not_le_of_gt $ mem_fin_pairs_lt.1 hab)]
  else by rw [sign_bij_aux, if_pos (le_of_not_gt h), dif_neg h, apply_inv_self,
    apply_inv_self, if_pos (le_of_lt $ mem_fin_pairs_lt.1 hab)])
sign_bij_aux_inj
sign_bij_aux_surj

lemma sign_aux_mul {n : ℕ} (f g : perm (fin n)) :
  sign_aux (f * g) = sign_aux f * sign_aux g :=
sign_aux_inv g ▸ begin
  unfold sign_aux,
  rw ← prod_mul_distrib,
  refine prod_bij (λ a ha, sign_bij_aux g a) sign_bij_aux_mem _ sign_bij_aux_inj sign_bij_aux_surj,
  rintros ⟨a, b⟩ hab,
  rw [sign_bij_aux, mul_apply, mul_apply],
  rw mem_fin_pairs_lt at hab,
  by_cases h : g b < g a,
  { rw dif_pos h,
    simp [not_le_of_gt hab]; congr },
  { rw [dif_neg h, inv_apply_self, inv_apply_self, if_pos (le_of_lt hab)],
    by_cases h₁ : f (g b) ≤ f (g a),
    { have : f (g b) ≠ f (g a),
      { rw [ne.def, injective.eq_iff f.bijective.1, 
          injective.eq_iff g.bijective.1];
        exact ne_of_lt hab },
      rw [if_pos h₁, if_neg (not_le_of_gt 
        (lt_of_le_of_ne h₁ this))],
      refl },
    { rw [if_neg h₁, if_pos (le_of_lt (lt_of_not_ge h₁))],
      refl } }
end

@[simp] lemma if_ne_neg {α : Type} {p : Prop} [decidable p] {a b : α} :
  (if p then a else b) ≠ b ↔ p ∧ a ≠ b :=
(decidable.em p).elim (λ hp, by simp [hp]) (λ hp, by simp [hp])

@[simp] lemma if_ne_pos {α : Type} {p : Prop} [decidable p] {a b : α} :
  (if p then a else b) ≠ a ↔ ¬p ∧ b ≠ a :=
(decidable.em p).elim (λ hp, by simp [hp]) (λ hp, by simp [hp])

@[simp] lemma dif_ne_neg {α : Type} {p : Prop} [decidable p] {a : p → α} {b : α} :
  (if hp : p then a hp else b) ≠ b ↔ ∃ hp : p, a hp ≠ b :=
(decidable.em p).elim (λ hp, by simp [hp]) (λ hp, by simp [hp])

@[simp] lemma dif_ne_pos {α : Type} {p : Prop} [decidable p] {a : α} {b : ¬p → α} :
  (if hp : p then a else b hp) ≠ a ↔ ∃ hp : ¬p, b hp ≠ a :=
(decidable.em p).elim (λ hp, by simp [hp]) (λ hp, by simp [hp])

private lemma sign_aux_transpose_zero_one {n : ℕ} (hn : 2 ≤ n) :
  sign_aux (transpose (⟨0, lt_of_lt_of_le dec_trivial hn⟩ : fin n) 
  ⟨1, lt_of_lt_of_le dec_trivial hn⟩) = -1 :=
let zero : fin n := ⟨0, lt_of_lt_of_le dec_trivial hn⟩ in
let one : fin n := ⟨1, lt_of_lt_of_le dec_trivial hn⟩ in
have hzo : zero < one := dec_trivial,
show sign_aux (transpose zero one) = sign_aux (transpose 
  (⟨0, dec_trivial⟩ : fin 2) ⟨1, dec_trivial⟩),
begin
  refine eq.symm (prod_bij_ne_one (λ _ _ _, ⟨one, zero⟩) 
    (λ _ _ _, mem_fin_pairs_lt.2 hzo) dec_trivial
    (λ a ha₁ ha₂, ⟨⟨⟨1, dec_trivial⟩, ⟨0, dec_trivial⟩⟩, dec_trivial, dec_trivial, _⟩)
    dec_trivial),
  replace ha₂ : ite (a.fst = zero) one (ite (a.fst = one) zero (a.fst)) ≤ 
    ite (a.snd = zero) one (ite (a.snd = one) zero (a.snd)):= (if_ne_neg.1 ha₂).1,
  replace ha₁ := mem_fin_pairs_lt.1 ha₁,
  cases a with a₁ a₂,
  have : ¬ one ≤ zero := dec_trivial,
  have : ∀ a : fin n, ¬a < zero := λ a, nat.not_lt_zero a.1,
  have : a₂ < one → a₂ = zero := λ h, fin.eq_of_veq (nat.le_zero_iff.1 (nat.le_of_lt_succ h)),
  have : a₁ ≤ one → a₁ = zero ∨ a₁ = one := fin.cases_on a₁ 
    (λ a, nat.cases_on a (λ _ _, or.inl dec_trivial) 
    (λ a, nat.cases_on a (λ _ _, or.inr dec_trivial)
    (λ _ _ h, absurd h dec_trivial))),
  have : a₁ ≤ zero → a₁ = zero := fin.eq_of_veq ∘ nat.le_zero_iff.1,
  have : a₁ ≤ a₂ → a₂ < a₁ → false := not_lt_of_ge,
  split_ifs at ha₂;
  simp [*, lt_irrefl, -not_lt] at *
end

lemma sign_aux_transpose : ∀ {n : ℕ} {x y : fin n} (hxy : x ≠ y),
  sign_aux (transpose x y) = -1
| 0 := dec_trivial
| 1 := dec_trivial
| (n+2) := λ x y hxy, 
let ⟨f, hf⟩ := transpose_conj hxy (show (⟨0, dec_trivial⟩ : fin (n + 2)) ≠
  ⟨1, dec_trivial⟩, from dec_trivial) in
have h2n : 2 ≤ n + 2 := dec_trivial,
by rw [← hf, sign_aux_mul, sign_aux_mul, sign_aux_transpose_zero_one h2n,
  mul_right_comm, ← sign_aux_mul, mul_inv_self, sign_aux_one, one_mul]

def sign [fintype α] [decidable_eq α] (x : perm α) : mu2 :=
trunc.lift
  (λ f : α ≃ fin (fintype.card α), sign_aux ((f.symm.trans x).trans f)) 
  (λ f g, calc sign_aux ((f.symm.trans x).trans f) =
    sign_aux (f.symm.trans g * (f.symm.trans x).trans f * (f.symm.trans g)⁻¹) :
      by rw [sign_aux_mul, sign_aux_mul, mul_right_comm, ← sign_aux_mul, 
        mul_inv_self, sign_aux_one, one_mul]
  ... = sign_aux (equiv.trans (equiv.trans (equiv.symm g) x) g) : congr_arg sign_aux
    $ equiv.ext _ _ $ λ a,
      by rw inv_def; simp[equiv.symm.trans_apply])
(fintype.equiv_fin α)

instance [fintype α] [decidable_eq α] : is_group_hom (@sign α _ _) :=
⟨λ x y, by unfold sign; exact
trunc.induction_on (fintype.equiv_fin α)
(λ f, begin
  simp only [trunc.lift_beta, mul_def],
  rw ← sign_aux_mul,
  exact congr_arg sign_aux (equiv.ext _ _ (λ x, by simp))
end)⟩

@[simp] lemma sign_transpose [fintype α] [decidable_eq α] {x y : α} (h : x ≠ y) :
  sign (transpose x y) = -1 :=
begin
  unfold sign,
  refine trunc.induction_on (fintype.equiv_fin α) (λ f, _),
  have : (f.symm.trans (transpose x y)).trans f = transpose (f x) (f y),
    from equiv.ext _ _ (λ b, begin 
      rw [transpose, transpose],
      simp,
      have : ∀ z : α, f.symm b = z → b = f z := 
        λ z hz, by simp [hz.symm],
      split_ifs; simp * at *
     end),
  rw [trunc.lift_beta, this,
    sign_aux_transpose (mt (injective.eq_iff f.bijective.1).1 h)]
end

def is_transposition [decidable_eq α] (f : perm α) := ∃ x y : α, f = transpose x y

def is_cycle (f : perm α) := ∃ x : α, ∀ y : α, ∃ n : ℕ, (f ^ n) x = y

def support [fintype α] [decidable_eq α] (f : perm α) := (@univ α _).filter (λ x, f x ≠ x)

@[simp] lemma mem_support_iff [fintype α] [decidable_eq α] {f : perm α} {a : α} :
  a ∈ f.support ↔ f a ≠ a := by simp [support]

lemma support_eq_empty [fintype α] [decidable_eq α] {f : perm α} :
  f.support = ∅ ↔ f = 1 :=
⟨λ h, equiv.ext _ _ (by simpa using h), λ h, by simp [h]⟩

def transpositions_list [fintype α] [decidable_eq α] 
  [decidable_linear_order α] : Π f : perm α,
  {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_transposition g}
| f := if h : f = 1 then ⟨[], eq.symm $ support_eq_empty.1 (by simp [h]), by simp⟩
  else
  let m := @option.get _ f.support.min (option.is_some_iff_exists.2 
    (let ⟨a, ha⟩ := exists_mem_of_ne_empty (mt support_eq_empty.1 h) in min_of_mem ha)) in
  have hm : f m ≠ m := mem_support_iff.1 (mem_of_min (option.get_mem _)),
  have wf : ((transpose m (f m))⁻¹ * f).support.card < f.support.card := 
    card_lt_card ⟨λ x hx, mem_support_iff.2 begin
      rw [mem_support_iff] at hx,
      clear transpositions_list,
      dsimp [transpose_apply, mul_apply] at *,
      split_ifs at hx with h h h,
      { assume hfxx,
        rw h at hfxx,
        rw hfxx at hm h,
        contradiction },
      { exact (hx ((injective.eq_iff f.bijective.1).1 h).symm).elim },
      { cc }
    end, 
    not_forall.2 ⟨m, by clear transpositions_list; simpa [mem_support_iff]⟩⟩,
  let l := transpositions_list ((transpose m (f m))⁻¹ * f) in
  ⟨transpose m (f m) :: l.1,
  by rw [list.prod_cons, l.2.1, ← mul_assoc, mul_inv_self, one_mul],
  λ g hg, ((list.mem_cons_iff _ _ _).1 hg).elim (λ hgt, ⟨m, f m, hgt⟩) 
    (l.2.2 _)⟩
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ f, f.support.card)⟩]}

def trunc_transpositions_list [fintype α] [decidable_eq α] (f : perm α) :
  trunc {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_transposition g} :=
trunc.rec_on_subsingleton (trunc_decidable_linear_order_fintype α)
(λ I, by exactI trunc.mk (transpositions_list f))

end equiv.perm