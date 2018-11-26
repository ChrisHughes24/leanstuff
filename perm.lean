/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.fintype group_theory.order_of_element

universes u v
open equiv function finset fintype
variables {α : Type u} {β : Type v}

def subtype_perm (f : perm α) {p : α → Prop} (h : ∀ x, p x ↔ p (f x)) : perm {x // p x} :=
⟨λ x, ⟨f x, (h _).1 x.2⟩, λ x, ⟨f⁻¹ x, (h (f⁻¹ x)).2 $ by simpa using x.2⟩,
  λ _, by simp, λ _, by simp⟩

def of_subtype {p : α → Prop} [decidable_pred p] (f : perm (subtype p)) : perm α :=
⟨λ x, if h : p x then f ⟨x, h⟩ else x, λ x, if h : p x then f⁻¹ ⟨x, h⟩ else x,
  λ x, have h : ∀ h : p x, p (f ⟨x, h⟩), from λ h, (f ⟨x, h⟩).2,
    by simp; split_ifs at *; simp * at *,
  λ x, have h : ∀ h : p x, p (f⁻¹ ⟨x, h⟩), from λ h, (f⁻¹ ⟨x, h⟩).2,
    by simp; split_ifs at *; simp * at *⟩

instance of_subtype.is_group_hom {p : α → Prop} [decidable_pred p] : is_group_hom (@of_subtype α p _) :=
⟨λ f g, equiv.ext _ _ $ λ x, begin
  rw [of_subtype, of_subtype, of_subtype],
  by_cases h : p x,
  { have h₁ : p (f (g ⟨x, h⟩)), from (f (g ⟨x, h⟩)).2,
    have h₂ : p (g ⟨x, h⟩), from (g ⟨x, h⟩).2,
    simp [h, h₁, h₂] },
  { simp [h] }
end⟩

def is_cycle (f : perm α) := ∃ x, f x ≠ x ∧ ∀ y, f y ≠ y → ∃ i : ℤ, (f ^ i) x = y

lemma of_subtype_subtype_perm {f : perm α} {p : α → Prop} [decidable_pred p] (h₁ : ∀ x, p x ↔ p (f x))
  (h₂ : ∀ x, f x ≠ x → p x) : of_subtype (subtype_perm f h₁) = f :=
equiv.ext _ _ $ λ x, begin
  rw [of_subtype, subtype_perm],
  by_cases hx : p x,
  { simp [hx] },
  { haveI := classical.prop_decidable,
    simp [hx, not_not.1 (mt (h₂ x) hx)] }
end

namespace equiv.perm
section sign
variable [decidable_eq α]

def is_swap (f : perm α) := ∃ x y, x ≠ y ∧ f = swap x y

def support [fintype α] (f : perm α) := univ.filter (λ x, f x ≠ x)

@[simp] lemma mem_support [fintype α] {f : perm α} {x : α} : x ∈ f.support ↔ f x ≠ x :=
by simp [support]

lemma support_swap_mul {f : perm α} {x : α}
  {y : α} (hy : (swap x (f x) * f) y ≠ y) : f y ≠ y ∧ y ≠ x :=
begin
  simp only [swap_apply_def, mul_apply, injective.eq_iff f.bijective.1] at *,
  by_cases h : f y = x,
  { split; intro; simp * at * },
  { split_ifs at hy; cc }
end

def swap_factors_aux : Π (l : list α) (f : perm α), (∀ {x}, f x ≠ x → x ∈ l) →
  {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g}
| []       := λ f h, ⟨[], equiv.ext _ _ $ λ x, by rw [list.prod_nil];
    exact eq.symm (not_not.1 (mt h (list.not_mem_nil _))), by simp⟩
| (x :: l) := λ f h,
if hfx : x = f x
then swap_factors_aux l f
  (λ y hy, list.mem_of_ne_of_mem (λ h : y = x, by simpa [h, hfx.symm] using hy) (h hy))
else let m := swap_factors_aux l (swap x (f x) * f)
      (λ y hy, have f y ≠ y ∧ y ≠ x, from support_swap_mul hy,
        list.mem_of_ne_of_mem this.2 (h this.1)) in
  ⟨swap x (f x) :: m.1,
  by rw [list.prod_cons, m.2.1, ← mul_assoc,
    mul_def (swap x (f x)), swap_swap, ← one_def, one_mul],
  λ g hg, ((list.mem_cons_iff _ _ _).1 hg).elim (λ h, ⟨x, f x, hfx, h⟩) (m.2.2 _)⟩

/-- `swap_factors` represents a permutation as a product of a list of transpositions.
The representation is non unique and depends on the linear order structure.
For types without linear order `trunc_swap_factors` can be used -/
def swap_factors [fintype α] [decidable_linear_order α] (f : perm α) :
  {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g} :=
swap_factors_aux ((@univ α _).sort (≤)) f (λ _ _, (mem_sort _).2 (mem_univ _))

def trunc_swap_factors [fintype α] (f : perm α) :
  trunc {l : list (perm α) // l.prod = f ∧ ∀ g ∈ l, is_swap g} :=
quotient.rec_on_subsingleton (@univ α _).1
(λ l h, trunc.mk (swap_factors_aux l f h))
(show ∀ x, f x ≠ x → x ∈ (@univ α _).1, from λ _ _, mem_univ _)

lemma swap_mul_swap_mul_swap {x y z : α} (hwz: x ≠ y) (hxz : x ≠ z) :
  swap y z * swap x y * swap y z = swap z x :=
equiv.ext _ _ $ λ n, by simp only [swap_apply_def, mul_apply]; split_ifs; cc

lemma is_conj_swap {w x y z : α} (hwx : w ≠ x) (hyz : y ≠ z) : is_conj (swap w x) (swap y z) :=
have h : ∀ {y z : α}, y ≠ z → w ≠ z →
    (swap w y * swap x z) * swap w x * (swap w y * swap x z)⁻¹ = swap y z :=
  λ y z hyz hwz, by rw [mul_inv_rev, swap_inv, swap_inv, mul_assoc (swap w y),
    mul_assoc (swap w y),  ← mul_assoc _ (swap x z), swap_mul_swap_mul_swap hwx hwz,
    ← mul_assoc, swap_mul_swap_mul_swap hwz.symm hyz.symm],
if hwz : w = z
then have hwy : w ≠ y, by cc,
  ⟨swap w z * swap x y, by rw [swap_comm y z, h hyz.symm hwy]⟩
else ⟨swap w y * swap x z, h hyz hwz⟩

section sign_aux
variables [fintype α] [decidable_linear_order α]

/-- set of all pairs (⟨a, b⟩ : Σ a : α, α) such that b < a -/
def pairs_lt (α : Type*) [fintype α] [decidable_linear_order α] : finset (α × α) :=
(univ : finset (α × α)).filter (λ a, a.2 < a.1)

lemma mem_fin_pairs_lt {a : α × α} :
  a ∈ pairs_lt α ↔ a.2 < a.1 :=
by simp [pairs_lt]

def sign_aux (a : perm α) : units ℤ :=
(pairs_lt α).prod (λ x, if a x.1 ≤ a x.2 then -1 else 1)

@[simp] lemma sign_aux_one : sign_aux (1 : perm α) = 1 :=
begin
  unfold sign_aux,
  conv { to_rhs, rw ← @finset.prod_const_one _ (units ℤ)
    (pairs_lt α) },
  exact finset.prod_congr rfl (λ a ha, if_neg
    (not_le_of_gt (mem_fin_pairs_lt.1 ha)))
end

def sign_bij_aux (f : perm α) (a : α × α) : α × α :=
if hxa : f a.2 < f a.1 then ⟨f a.1, f a.2⟩ else ⟨f a.2, f a.1⟩

lemma sign_bij_aux_inj {f : perm α} : ∀ a b : α × α,
   a ∈ pairs_lt α → b ∈ pairs_lt α →
   sign_bij_aux f a = sign_bij_aux f b → a = b :=
λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb h, begin
  unfold sign_bij_aux at h,
  rw mem_fin_pairs_lt at *,
  have : ¬b₁ < b₂ := not_lt_of_ge (le_of_lt hb),
  split_ifs at h;
  simp [*, injective.eq_iff f.bijective.1, sigma.mk.inj_eq] at *
end

lemma sign_bij_aux_surj {f : perm α} : ∀ a ∈ pairs_lt α,
  ∃ b ∈ pairs_lt α, a = sign_bij_aux f b :=
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

lemma sign_bij_aux_mem {f : perm α} : ∀ a : α × α,
  a ∈ pairs_lt α → sign_bij_aux f a ∈ pairs_lt α :=
λ ⟨a₁, a₂⟩ ha, begin
  unfold sign_bij_aux,
  split_ifs with h,
  { exact mem_fin_pairs_lt.2 h },
  { exact mem_fin_pairs_lt.2
    (lt_of_le_of_ne (le_of_not_gt h)
      (λ h, ne_of_lt (mem_fin_pairs_lt.1 ha) (f.bijective.1 h.symm))) }
end

@[simp] lemma sign_aux_inv (f : perm α) : sign_aux f⁻¹ = sign_aux f :=
prod_bij (λ a ha, sign_bij_aux f⁻¹ a)
sign_bij_aux_mem
(λ ⟨a, b⟩ hab, if h : f⁻¹ b < f⁻¹ a
  then by rw [sign_bij_aux, dif_pos h, if_neg (not_le_of_gt h), apply_inv_self,
    apply_inv_self, if_neg (not_le_of_gt $ mem_fin_pairs_lt.1 hab)]
  else by rw [sign_bij_aux, if_pos (le_of_not_gt h), dif_neg h, apply_inv_self,
    apply_inv_self, if_pos (le_of_lt $ mem_fin_pairs_lt.1 hab)])
sign_bij_aux_inj
sign_bij_aux_surj

lemma sign_aux_mul (f g : perm α) : sign_aux (f * g) = sign_aux f * sign_aux g :=
begin
  rw ← sign_aux_inv g,
  unfold sign_aux,
  rw  ← prod_mul_distrib,
  refine prod_bij (λ a ha, sign_bij_aux g a) sign_bij_aux_mem _
    sign_bij_aux_inj sign_bij_aux_surj,
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
      rw [if_pos h₁, if_neg (not_le_of_gt  (lt_of_le_of_ne h₁ this))],
      refl },
    { rw [if_neg h₁, if_pos (le_of_lt (lt_of_not_ge h₁))],
      refl } }
end

instance sign_aux.is_group_hom : is_group_hom (@sign_aux α _ _ _) := ⟨sign_aux_mul⟩

private lemma sign_aux_swap_zero_one {n : ℕ} (hn : 2 ≤ n) :
  sign_aux (swap (⟨0, lt_of_lt_of_le dec_trivial hn⟩ : fin n)
  ⟨1, lt_of_lt_of_le dec_trivial hn⟩) = -1 :=
let zero : fin n := ⟨0, lt_of_lt_of_le dec_trivial hn⟩ in
let one : fin n := ⟨1, lt_of_lt_of_le dec_trivial hn⟩ in
have hzo : zero < one := dec_trivial,
show _ = (finset.singleton (⟨one, zero⟩ : fin n × fin n)).prod
  (λ x : fin n × fin n, if (equiv.swap zero one) x.1
  ≤ swap zero one x.2 then (-1 : units ℤ) else 1),
begin
  refine eq.symm (prod_subset (λ ⟨x₁, x₂⟩, by simp [mem_fin_pairs_lt, hzo] {contextual := tt})
    (λ a ha₁ ha₂, _)),
  rcases a with ⟨⟨a₁, ha₁⟩, ⟨a₂, ha₂⟩⟩,
  replace ha₁ : a₂ < a₁ := mem_fin_pairs_lt.1 ha₁,
  simp only [swap_apply_def],
  have : ¬ 1 ≤ a₂ → a₂ = 0, from λ h, nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge h)),
  have : a₁ ≤ 1 → a₁ = 0 ∨ a₁ = 1, from nat.cases_on a₁ (λ _, or.inl rfl)
    (λ a₁, nat.cases_on a₁ (λ _, or.inr rfl) (λ _ h, absurd h dec_trivial)),
  split_ifs;
  simp [*, lt_irrefl, -not_lt, not_le.symm, -not_le, le_refl, fin.lt_def, fin.le_def, nat.zero_le,
    zero, one, iff.intro fin.veq_of_eq fin.eq_of_veq, nat.le_zero_iff] at *,
end

lemma sign_aux_swap : ∀ {n : ℕ} {x y : fin n} (hxy : x ≠ y), sign_aux (swap x y) = -1
| 0 := dec_trivial
| 1 := dec_trivial
| (n+2) := λ x y hxy,
have h2n : 2 ≤ n + 2 := dec_trivial,
by rw [← is_conj_iff_eq, ← sign_aux_swap_zero_one h2n];
  exact is_group_hom.is_conj _ (is_conj_swap hxy dec_trivial)

end sign_aux

def sign_aux2 : list α → perm α → units ℤ
| []     f := 1
| (x::l) f := if x = f x then sign_aux2 l f else -sign_aux2 l (swap x (f x) * f)

lemma sign_aux_eq_sign_aux2 {n : ℕ} : ∀ (l : list α) (f : perm α) (e : α ≃ fin n)
  (h : ∀ x, f x ≠ x → x ∈ l), sign_aux ((e.symm.trans f).trans e) = sign_aux2 l f
| []     f e h := have f = 1, from equiv.ext _ _ $
  λ y, not_not.1 (mt (h y) (list.not_mem_nil _)),
by rw [this, one_def, equiv.trans_refl, equiv.symm_trans, ← one_def,
  sign_aux_one, sign_aux2]
| (x::l) f e h := begin
  rw sign_aux2,
  by_cases hfx : x = f x,
  { rw if_pos hfx,
    exact sign_aux_eq_sign_aux2 l f _ (λ y (hy : f y ≠ y), list.mem_of_ne_of_mem
      (λ h : y = x, by simpa [h, hfx.symm] using hy) (h y hy) ) },
  { have hy : ∀ y : α, (swap x (f x) * f) y ≠ y → y ∈ l,
      from λ y hy, have f y ≠ y ∧ y ≠ x, from support_swap_mul hy,
      list.mem_of_ne_of_mem this.2 (h _ this.1),
    have : (e.symm.trans (swap x (f x) * f)).trans e =
      (swap (e x) (e (f x))) * (e.symm.trans f).trans e,
      from equiv.ext _ _ (λ z, by rw ← equiv.symm_trans_swap_trans; simp [mul_def]),
    have hefx : e x ≠ e (f x), from mt (injective.eq_iff e.bijective.1).1 hfx,
    rw [if_neg hfx, ← sign_aux_eq_sign_aux2 _ _ e hy, this, sign_aux_mul, sign_aux_swap hefx],
    simp }
end

def sign_aux3 [fintype α] (f : perm α) {s : multiset α} : (∀ x, x ∈ s) → units ℤ :=
quotient.hrec_on s (λ l h, sign_aux2 l f)
  (trunc.induction_on (equiv_fin α)
    (λ e l₁ l₂ h, function.hfunext
      (show (∀ x, x ∈ l₁) = ∀ x, x ∈ l₂, by simp [list.mem_of_perm h])
      (λ h₁ h₂ _, by rw [← sign_aux_eq_sign_aux2 _ _ e (λ _ _, h₁ _),
        ← sign_aux_eq_sign_aux2 _ _ e (λ _ _, h₂ _)])))

lemma sign_aux3_mul_and_swap [fintype α] (f g : perm α) (s : multiset α) (hs : ∀ x, x ∈ s) :
  sign_aux3 (f * g) hs = sign_aux3 f hs * sign_aux3 g hs ∧ ∀ x y, x ≠ y →
  sign_aux3 (swap x y) hs = -1 :=
let ⟨l, hl⟩ := quotient.exists_rep s in
let ⟨e, _⟩ := trunc.exists_rep (equiv_fin α) in
begin
  clear _let_match _let_match,
  subst hl,
  show sign_aux2 l (f * g) = sign_aux2 l f * sign_aux2 l g ∧
    ∀ x y, x ≠ y → sign_aux2 l (swap x y) = -1,
  have hfg : (e.symm.trans (f * g)).trans e = (e.symm.trans f).trans e * (e.symm.trans g).trans e,
    from equiv.ext _ _ (λ h, by simp [mul_apply]),
  split,
  { rw [← sign_aux_eq_sign_aux2 _ _ e (λ _ _, hs _), ← sign_aux_eq_sign_aux2 _ _ e (λ _ _, hs _),
      ← sign_aux_eq_sign_aux2 _ _ e (λ _ _, hs _), hfg, sign_aux_mul] },
  { assume x y hxy,
    have hexy : e x ≠ e y, from mt (injective.eq_iff e.bijective.1).1 hxy,
    rw [← sign_aux_eq_sign_aux2 _ _ e (λ _ _, hs _), equiv.symm_trans_swap_trans, sign_aux_swap hexy] }
end

/-- `sign` of a permutation returns the signature or parity of a permutation, `1` for even
permutations, `-1` for odd permutations. It is the unique surjective group homomorphism from
`perm α` to the group with two elements.-/
def sign [fintype α] (f : perm α) := sign_aux3 f mem_univ

instance sign.is_group_hom [fintype α] : is_group_hom (@sign α _ _) :=
⟨λ f g, (sign_aux3_mul_and_swap f g _ mem_univ).1⟩

lemma sign_swap [fintype α] {x y : α} (h : x ≠ y) : sign (swap x y) = -1 :=
(sign_aux3_mul_and_swap 1 1 _ mem_univ).2 x y h

@[simp] lemma sign_mul [fintype α] (f g : perm α) : sign (f * g) = sign f * sign g :=
is_group_hom.mul sign _ _

lemma units_int_inv_eq_self : ∀ u : units ℤ, u⁻¹ = u := dec_trivial

@[simp] lemma sign_inv [fintype α] (f : perm α) : sign f⁻¹ = sign f :=
(is_group_hom.inv sign f).symm ▸ units_int_inv_eq_self _

@[simp] lemma sign_one [fintype α] : sign (1 : perm α) = 1 :=
is_group_hom.one _

lemma sign_eq_of_is_swap [fintype α] {f : perm α} (h : is_swap f) : sign f = -1 :=
let ⟨x, y, hxy⟩ := h in hxy.2.symm ▸ sign_swap hxy.1

lemma sign_eq_pow_length_swap_factors [fintype α] {f : perm α} {l : list (perm α)}
  (h : l.prod = f) (hl : ∀ g ∈ l, is_swap g) : sign f = -1 ^ l.length :=
have h₁ : l.map sign = list.repeat (-1) l.length :=
  list.eq_repeat.2 ⟨by simp, λ u hu,
  let ⟨g, hg⟩ := list.mem_map.1 hu in
  hg.2 ▸ sign_eq_of_is_swap (hl _ hg.1)⟩,
by rw [← list.prod_repeat, ← h₁, ← is_group_hom.prod (@sign α _ _), h]

lemma sign_symm_trans_trans [fintype α] [decidable_eq β] [fintype β] (f : perm α)
  (e : α ≃ β) : sign ((e.symm.trans f).trans e) = sign f :=
show sign_aux3 ((e.symm.trans f).trans e) (show ∀ x : β, x ∈ univ.1, from mem_univ) =
  sign_aux3 f (show ∀ x : α, x ∈ univ.1, from mem_univ),
from quotient.induction_on₂ (@univ β _).1 (@univ α _).1
  (λ l₁ l₂ h₁ h₂, show sign_aux2 _ _ = sign_aux2 _ _,
    from let n := trunc.out (equiv_fin β) in
    by rw [← sign_aux_eq_sign_aux2 _ _ n (λ _ _, h₁ _),
        ← sign_aux_eq_sign_aux2 _ _ (e.trans n) (λ _ _, h₂ _)];
      exact congr_arg sign_aux (equiv.ext _ _ (λ x, by simp)))
(show ∀ x : β, x ∈ univ.1, from mem_univ)
(show ∀ x : α, x ∈ univ.1, from mem_univ)

lemma eq_sign_of_surjective_hom [fintype α] {s : perm α → units ℤ}
  [is_group_hom s] (hs : surjective s) : s = sign :=
have ∀ {f}, is_swap f → s f = -1 :=
  λ f ⟨x, y, hxy, hxy'⟩, hxy'.symm ▸ by_contradiction (λ h,
    have ∀ f, is_swap f → s f = 1 := λ f ⟨a, b, hab, hab'⟩,
      by rw [← is_conj_iff_eq, ← or.resolve_right (int.units_eq_one_or _) h, hab'];
        exact is_group_hom.is_conj _ (is_conj_swap hab hxy),
  let ⟨g, hg⟩ := hs (-1) in
  let ⟨l, hl⟩ := trunc.out (trunc_swap_factors g) in
  have ∀ a ∈ l.map s, a = (1 : units ℤ) := λ a ha,
    let ⟨g, hg⟩ := list.mem_map.1 ha in hg.2 ▸ this _ (hl.2 _ hg.1),
  have s l.prod = 1,
    by rw [is_group_hom.prod s, list.eq_repeat'.2 this, list.prod_repeat, one_pow],
  by rw [hl.1, hg] at this;
    exact absurd this dec_trivial),
funext $ λ f,
let ⟨l, hl₁, hl₂⟩ := trunc.out (trunc_swap_factors f) in
have hsl : ∀ a ∈ l.map s, a = (-1 : units ℤ) := λ a ha,
  let ⟨g, hg⟩ := list.mem_map.1 ha in hg.2 ▸  this (hl₂ _ hg.1),
by rw [← hl₁, is_group_hom.prod s, list.eq_repeat'.2 hsl, list.length_map,
     list.prod_repeat, hl₁, sign_eq_pow_length_swap_factors hl₁ hl₂]

lemma prod_units_eq_pow_card_neg_one {s : finset α} (f : α → units ℤ) :
  s.prod f = -1 ^ (s.filter (λ a, f a = -1)).card :=
by rw [← finset.prod_const];
  exact eq.symm (prod_bij_ne_one (λ a _ _, a) (by finish) (by simp)
    (λ b _ h, ⟨b, by simp [or.resolve_left (int.units_eq_one_or (f b)) h, *,
      show (-1 : units ℤ) ≠ 1, from dec_trivial]⟩) (by simp {contextual := tt}))

instance [subsingleton α] : subsingleton (perm α) :=
⟨λ _ _, equiv.ext _ _ $ λ _, subsingleton.elim _ _⟩

lemma sign_eq_pow_card_inversions [decidable_linear_order α] [fintype α] (f : perm α) :
  sign f = -1 ^ ((pairs_lt α).filter (λ a : α × α, a.1 ≤ a.2)).card := sorry

lemma is_swap_of_subtype [decidable_eq α] {p : α → Prop} [decidable_pred p]
  {f : perm (subtype p)} (h : is_swap f) : is_swap (of_subtype f) :=
let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h in
⟨x, y, by simp at hxy; tauto,
  equiv.ext _ _ $ λ z, begin
    rw [hxy.2, of_subtype],
    simp [swap_apply_def],
    split_ifs;
    cc <|> simp * at *
  end⟩

lemma int.units_pow_eq_pow_mod_two (u : units ℤ) (n : ℕ) : u ^ n = u ^ (n % 2) :=
(int.units_eq_one_or u).elim (λ h, by simp *)
  (λ h, by conv {to_lhs, rw [← nat.mod_add_div n 2, pow_add, pow_mul, h, pow_two]};
          simp [h])

lemma sign_subtype_perm [fintype α] [decidable_eq α] (f : perm α) {p : α → Prop} [decidable_pred p]
  (h₁ : ∀ x, p x ↔ p (f x)) (h₂ : ∀ x, f x ≠ x → p x) : sign (subtype_perm f h₁) = sign f :=
let l := trunc.out (trunc_swap_factors (subtype_perm f h₁)) in
have hl' : ∀ g' ∈ l.1.map of_subtype, is_swap g' :=
  λ g' hg',
  let ⟨g, hg⟩ := list.mem_map.1 hg' in
  hg.2 ▸ is_swap_of_subtype (l.2.2 _ hg.1),
have hl'₂ : (l.1.map of_subtype).prod = f,
  by rw [← is_group_hom.prod of_subtype l.1, l.2.1, of_subtype_subtype_perm _ h₂],
by rw [sign_eq_pow_length_swap_factors l.2.1 l.2.2, sign_eq_pow_length_swap_factors hl'₂ hl'];
  simp

lemma is_cycle_swap {x y : α} (hxy : x ≠ y) : is_cycle (swap x y) :=
⟨y, by rwa swap_apply_right,
λ a (ha : ite (a = x) y (ite (a = y) x a) ≠ a),
if hya : y = a then ⟨0, hya⟩
  else ⟨1, by rw [gpow_one, swap_apply_def]; split_ifs at *; cc⟩⟩

lemma eq_inv_iff_eq {f : perm α} {x y : α} : x = f⁻¹ y ↔ f x = y :=
by conv {to_lhs, rw [← injective.eq_iff f.bijective.1, apply_inv_self]}

lemma inv_eq_iff_eq {f : perm α} {x y : α} : f⁻¹ x =  y ↔ x = f y :=
by rw [eq_comm, eq_inv_iff_eq, eq_comm]

lemma is_cycle_inv {f : perm α} (hf : is_cycle f) : is_cycle (f⁻¹) :=
let ⟨x, hx⟩ := hf in
⟨x, by simp [eq_inv_iff_eq, inv_eq_iff_eq, *] at *; cc,
  λ y hy, let ⟨i, hi⟩ := hx.2 y (by simp [eq_inv_iff_eq, inv_eq_iff_eq, *] at *; cc) in
  ⟨-i, by rwa [gpow_neg, inv_gpow, inv_inv]⟩⟩

lemma swap_mul (f : perm α) (x y : α) : swap x y * f = f * swap (f⁻¹ x) (f⁻¹ y) :=
equiv.ext _ _ $ λ z, begin
  simp [mul_apply, swap_apply_def],
  split_ifs;
  simp [*, eq_inv_iff_eq] at * <|> cc
end

lemma mul_swap (f : perm α) (x y : α) : f * swap x y = swap (f x) (f y) * f :=
by rw [swap_mul, inv_apply_self, inv_apply_self]

lemma swap_mul_pow : ∀ (n : ℤ) {b x : α} {f : perm α} (hf : is_cycle f)
  (hb : (swap x (f x) * f) b ≠ b)
  (h : (f ^ n) (f x) = b), ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b
| 0         := λ b x f hf hb h, ⟨0, h⟩
| (n+1 : ℕ) := λ b x f hf hb h,
  if hfbx : f x = b then ⟨0, hfbx⟩ else
  have f b ≠ b ∧ b ≠ x := support_swap_mul hb,
  have hb : (swap x (f x) * f) (f⁻¹ b) ≠ f⁻¹ b,
    by rw [mul_apply, apply_inv_self, swap_apply_of_ne_of_ne this.2 (ne.symm hfbx),
        ne.def, ← injective.eq_iff f.bijective.1, apply_inv_self];
      exact this.1,
  have wf : n < int.nat_abs (1 + ↑n),
    by rw [add_comm, ← int.coe_nat_one, ← int.coe_nat_add, int.nat_abs_of_nat];
    exact nat.lt_succ_self n,
  let ⟨i, hi⟩ := swap_mul_pow n hf hb
    (f.bijective.1 $ by
      rw [apply_inv_self];
      rwa [gpow_coe_nat, pow_succ, mul_apply] at h) in
  ⟨i + 1, by rw [add_comm, gpow_add, mul_apply, hi, gpow_one, mul_apply, apply_inv_self,
      swap_apply_of_ne_of_ne this.2 (ne.symm hfbx)]⟩
| -[1+ n] := λ b x f hf hb h,
  if hfbx : f⁻¹ x = b then ⟨-1, by rwa [gpow_neg, gpow_one, mul_inv_rev, mul_apply, swap_inv, swap_apply_right]⟩
  else if hfbx' : f x = b then ⟨0, hfbx'⟩
  else
  have f b ≠ b ∧ b ≠ x := support_swap_mul hb,
  have hb : (swap x (f⁻¹ x) * f⁻¹) (f⁻¹ b) ≠ f⁻¹ b,
    by rw [mul_apply, swap_apply_def];
      split_ifs;
      simp [inv_eq_iff_eq, eq_inv_iff_eq] at *; cc,
  have wf : n < n.succ, from nat.lt_succ_self n,
  let ⟨i, hi⟩ := swap_mul_pow n (is_cycle_inv hf) hb
    (show (f⁻¹ ^ ↑n) (f⁻¹ x) = f⁻¹ b, by
      rw [← h, ← mul_apply, ← mul_apply, ← mul_apply, gpow_neg_succ, ← inv_pow, pow_succ', mul_assoc,
        mul_assoc, inv_mul_self, mul_one, gpow_coe_nat, ← pow_succ', ← pow_succ]) in
  have h : (swap x (f⁻¹ x) * f⁻¹) (f x) = f⁻¹ x, by rw [mul_apply, inv_apply_self, swap_apply_left],
  ⟨-i, by rw [← add_sub_cancel i 1, neg_sub, sub_eq_add_neg, gpow_add, gpow_one, gpow_neg, ← inv_gpow,
      mul_inv_rev, swap_inv, mul_swap, inv_apply_self, swap_comm _ x, gpow_add, gpow_one,
      mul_apply, mul_apply (_ ^ i), h, hi, mul_apply, apply_inv_self, swap_apply_of_ne_of_ne this.2 (ne.symm hfbx')]⟩
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf int.nat_abs⟩]}

lemma eq_swap_of_is_cycle_of_apply_apply_eq_self {f : perm α} (hf : is_cycle f) {x : α}
  (hfx : f x ≠ x) (hffx : f (f x) = x) : f = swap x (f x) :=
equiv.ext _ _ $ λ y,
have ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x :=
  λ n, nat.rec_on n (or.inl rfl)
    (λ n ih, ih.elim (λ h, or.inr (by rw [pow_succ, mul_apply, h]))
      (λ h, or.inl (by rw [pow_succ, mul_apply, h, hffx]))),
have ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x :=
  λ i, int.rec_on i this (λ n, by
  by rw [gpow_neg_succ, inv_eq_iff_eq, ← injective.eq_iff f.bijective.1, ← mul_apply, ← pow_succ,
    eq_comm, inv_eq_iff_eq, ← mul_apply, ← pow_succ', @eq_comm _ x, or.comm];
    exact this _),
let ⟨z, hz⟩ := hf in
let ⟨i, hi⟩ := hz.2 x hfx in
if hyx : y = x then by simp [hyx]
else if hfyx : y = f x then by simp [hfyx, hffx]
else begin
  rw [swap_apply_of_ne_of_ne hyx hfyx],
  refine by_contradiction (λ hy, _),
  cases hz.2 y hy with j hj,
  rw [← sub_add_cancel j i, gpow_add, mul_apply, hi] at hj,
  cases this (j - i) with hji hji,
  { rw [← hj, hji] at hyx, cc },
  { rw [← hj, hji] at hfyx, cc }
end

lemma is_cycle_swap_mul {f : perm α} (hf : is_cycle f) {x : α}
  (hx : f x ≠ x ∧ ∀ y, f y ≠ y → ∃ i : ℤ, (f ^ i) x = y) :
  is_cycle (swap x (f x) * f) ∨ swap x (f x) * f = 1 :=
if hffx : f (f x) = x
then or.inr $ calc
  swap x (f x) * f = swap x (f x) * swap x (f x) :
    by rw ← eq_swap_of_is_cycle_of_apply_apply_eq_self hf hx.1 hffx
  ... = 1 : swap_swap _ _
else or.inl
  ⟨f x, by simp only [swap_apply_def, mul_apply];
          split_ifs; simp [injective.eq_iff f.bijective.1] at *; cc,
    λ y hy,
    let ⟨i, hi⟩ := hx.2 _ (support_swap_mul hy).1 in
    have hi : (f ^ (i - 1)) (f x) = y, from
      calc (f ^ (i - 1)) (f x) = (f ^ (i - 1) * f ^ (1 : ℤ)) x : by rw [gpow_one, mul_apply]
      ... =  y : by rwa [← gpow_add, sub_add_cancel],
    swap_mul_pow (i-1) hf hy hi⟩

lemma support_swap_mul_cycle [fintype α] {f : perm α} (hf : is_cycle f) {x : α}
  (hx : f x ≠ x ∧ ∀ y, f y ≠ y → ∃ i : ℤ, (f ^ i) x = y) :
  (swap x (f x) * f).support = f.support.erase x ∨ swap x (f x) * f = 1 :=
or_iff_not_imp_right.2 (λ h1, finset.ext.2 $ λ y, begin
  have hfyxor : f y ≠ x ∨ f x ≠ y :=
    not_and_distrib.1 (λ h, h1 $
      by have := eq_swap_of_is_cycle_of_apply_apply_eq_self hf hx.1 (by rw [h.2, h.1]);
      rw [← this, this, mul_def, swap_swap, one_def]),
  rw [mem_support, mem_erase, mem_support],
  split,
  { assume h,
    refine not_or_distrib.1 (λ h₁, h₁.elim
      (λ hyx, by simpa [hyx, mul_apply] using h) _),
    assume hfy,
    have hyx : x ≠ y := λ h, by rw h at hx; tauto,
    have hfyx : f x ≠ y := by rwa [← hfy, ne.def, injective.eq_iff f.bijective.1],
    simpa [mul_apply, hfy, swap_apply_of_ne_of_ne hyx.symm hfyx.symm] using h },
  { assume h,
    simp [swap_apply_def],
    split_ifs; cc }
end)

lemma support_swap [fintype α] {x y : α} (hxy : x ≠ y) : (swap x y).support = {x, y} :=
finset.ext.2 $ λ a, by simp [swap_apply_def]; split_ifs; cc

@[simp] lemma card_support_swap [fintype α] {x y : α} (hxy : x ≠ y) : (swap x y).support.card = 2 :=
show (swap x y).support.card = finset.card ⟨x::y::0, by simp [hxy]⟩,
from congr_arg card $ by rw [support_swap hxy]; simp [*, finset.ext]; cc

lemma sign_cycle [fintype α] : ∀ {f : perm α} (hf : is_cycle f),
  sign f = -1 ^ (f.support.card + 1)
| f := λ hf,
let ⟨x, hx⟩ := hf in
calc sign f = sign (swap x (f x) * (swap x (f x) * f)) :
by rw [← mul_assoc, mul_def, mul_def, swap_swap, trans_refl]
... = -1 ^ (f.support.card + 1) :
if h1 : (swap x (f x) * f) = 1 then
have h : f = swap x (f x),
  by rwa [mul_eq_one_iff_inv_eq, swap_inv, eq_comm] at h1,
by rw [sign_mul, sign_swap hx.1.symm, h1, sign_one, h, card_support_swap hx.1.symm]; refl
else
  have h : card (support (swap x (f x) * f)) + 1 = card (support f),
    by rw [← insert_erase (mem_support.2 hx.1), or.resolve_right (support_swap_mul_cycle hf hx) h1,
      card_insert_of_not_mem (not_mem_erase _ _)],
  have wf : card (support (swap x (f x) * f)) < card (support f),
    from h ▸ nat.lt_succ_self _,
  by rw [sign_mul, sign_swap hx.1.symm, sign_cycle (or.resolve_right (is_cycle_swap_mul hf hx) h1), h];
    simp [pow_add]
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ f, f.support.card)⟩]}

end sign

end equiv.perm