import data.num.lemmas
lemma e : 12402536340 * 2356324602 = 29224401505141036680 :=
begin
  rw ← num.of_nat_inj,
  simp [num.bit0_of_bit0, num.bit1_of_bit1],
  refl
end
#print e
#exit
import data.equiv 

def is_valuation {R : Type} [comm_ring R] {α : Type} [linear_order α] (f : R → α) : Prop := true

structure valuations (R : Type) [comm_ring R] :=
(α : Type) [Hα : linear_order α] (f : R → α) (Hf : is_valuation f)

instance to_make_next_line_work (R : Type) [comm_ring R] (v : valuations R) : linear_order v.α := v.Hα

instance valuations.setoid (R : Type) [comm_ring R] : setoid (valuations R) := {
  r := λ v w, ∀ r s : R, valuations.f v r ≤ v.f s ↔ w.f r ≤ w.f s,
  iseqv := ⟨λ v r s,iff.rfl,λ v w H r s,(H r s).symm,λ v w x H1 H2 r s,iff.trans (H1 r s) (H2 r s)⟩
}

def Spv1 (R : Type) [comm_ring R] := quotient (valuations.setoid R)

def Spv2 (R : Type) [comm_ring R] := 
  {ineq : R → R → Prop // ∃ v : valuations R, ∀ r s : R, ineq r s ↔ v.f r ≤ v.f s}

#check Spv1 _ -- Type 1
#check Spv2 _ -- Type

def to_fun (R : Type) [comm_ring R] : Spv1 R → Spv2 R :=
quotient.lift (λ v, (⟨λ r s, valuations.f v r ≤ v.f s, ⟨v,λ r s,iff.rfl⟩⟩ : Spv2 R))
  (λ v w H,begin dsimp,congr,funext,exact propext (H r s) end) 

open function
noncomputable definition they_are_the_same (R : Type) [comm_ring R] : equiv (Spv1 R) (Spv2 R) :=
equiv.of_bijective $ show bijective (to_fun R),
from ⟨λ x y, quotient.induction_on₂ x y $ λ x y h,
  quotient.sound $ λ r s, iff_of_eq $ congr_fun (congr_fun (subtype.mk.inj h) r) s,
  λ ⟨x, ⟨v, hv⟩⟩, ⟨⟦v⟧, subtype.eq $ funext $ λ r, funext $ λ s, propext (hv r s).symm⟩⟩

noncomputable definition they_are_the_same (R : Type) [comm_ring R] : equiv (Spv1 R) (Spv2 R) :=
{ to_fun := to_fun R,
  inv_fun := inv_fun R,
  left_inv := λ vs, quotient.induction_on vs begin
    assume vs,
    apply quotient.sound,
    intros r s,
    have := (to_fun R ⟦vs⟧).property,
    have H := classical.some_spec (to_fun R ⟦vs⟧).property r s,
    refine H.symm.trans _,
    refl,
  end,
  right_inv := λ s2,begin
    cases s2 with rel Hrel,
    apply subtype.eq,
    dsimp,
    unfold inv_fun,
    funext r s,
    sorry
  end 
}

#exit
import logic.function data.set.basic set_theory.cardinal
universes u v w x
open function

lemma eq.rec_thing {α : Sort*} (a : α) (h : a = a) (C : α → Sort*) (b : C a) : (eq.rec b h : C a) = b := rfl

def T : Type 1 := Σ α : Type, set α

set_option trace.simplify.rewrite true
lemma Type_1_bigger {α : Type} {f : T → α} : ¬injective f :=
λ h, cantor_injective (f ∘ sigma.mk α) $ injective_comp h (by simp [injective])

theorem forall_2_true_iff2  {α : Sort u} {β : α → Sort v} : (∀ (a b : α), true) ↔ true :=
by rw [forall_true_iff, forall_true_iff]

theorem forall_2_true_iff3  {α : Sort u} {β : α → Sort v} : (∀ (a b : α), true) ↔ true :=
by simp only [forall_true_iff, forall_true_iff]

example {α : Type} {f : α → T} : ¬ surjective f :=
λ h, Type_1_bigger (injective_surj_inv h)

#exit
constant a : ℕ

lemma empty_implies_false (f : empty → empty) : f = id :=
funext $ λ x, by cases x

#print has_equiv

structure thing {R : Type} [ring R]
{ type : Type }
(  )

instance : has_repr pnat := subtype.has_repr

#eval ((@function.comp ℕ ℕ ℕ) ∘ (∘))

#print quotient.lift_on
noncomputable example (f : α → β) :
  quotient (fun_rel f) ≃ set.range f :=
@equiv.of_bijective _ _ (λ a, @quotient.lift_on _ _ (fun_rel f) a 
(λ a, show set.range f, from ⟨f a, set.mem_range_self _⟩)
(λ a b h, subtype.eq h))
⟨λ a b, @quotient.induction_on₂ _ _ (fun_rel f) (fun_rel f) _ a b begin
  assume a b h,
  exact quot.sound (subtype.mk.inj h),
end, λ ⟨a, ⟨x, ha⟩⟩, ⟨@quotient.mk _ (fun_rel f) x, by simp * ⟩⟩

noncomputable example {G H : Type*} [group G] [group H] (f : G → H) [is_group_hom f] :
  {x : left_cosets (ker f) ≃ set.range f // is_group_hom x} :=
⟨@equiv.of_bijective _ _ (λ a, @quotient.lift_on _ _ (left_rel (ker f)) a 
  (λ a, show set.range f, from ⟨f a, set.mem_range_self _⟩) 
    (λ a b h, subtype.eq begin 
    show f a = f b,
    rw [← one_mul b, ← mul_inv_self a, mul_assoc, is_group_hom.mul f, mem_trivial.1 h, mul_one],
  end)) ⟨λ a b, @quotient.induction_on₂ _ _(left_rel (ker f)) (left_rel (ker f)) _ a b 
  (begin
    assume a b h,
    have : f a = f b := subtype.mk.inj h,
    refine quot.sound (mem_trivial.2 _),
    rw [mul f, ← this, ← mul f, inv_mul_self, one f]
  end),
  λ ⟨a, ha⟩, 
  let ⟨x, hx⟩ := set.mem_range.1 ha in
  ⟨@quotient.mk _ (left_rel (ker f)) x, subtype.eq hx⟩⟩,
  ⟨λ a b, @quotient.induction_on₂ _ _(left_rel (ker f)) (left_rel (ker f)) _ a b begin 
    assume a b,
    rw equiv.of_bijective_to_fun,
    exact subtype.eq (mul f _ _),
  end⟩⟩
#print has_repr

instance : has_repr (finset α) :=

#exit
universes u v
axiom choice {α : Type u} (β : α → Type v) 
  (h : ∀ a : α, nonempty (β a)) : Π a, β a

example {α : Type u} : nonempty α → α :=
λ h, @choice unit (λ _, α) (λ _, h) ()

#print classical.axiom_of_choice

variable (α : Type)
def foo : semigroup α := 
begin
  refine_struct { .. },
end
variables {a b c : ℕ}

#print empty.elim
lemma empty_implies_false (f : empty → empty) : f = id :=
#print empty_implies_false

#eval list.foldr ((∘) : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ) id [nat.succ, nat.pred] 0

example (x : ℕ) (l : list ℕ) : list.prod (x :: l) = l.prod * x := rfl

example : list.prod [a, b, c] = sorry := begin
  unfold list.prod list.foldl,

end

#print list.prod
open set
local attribute [instance] classical.prop_decidable
example (a b : Prop) : ((a → b) → (a ↔ b)) ↔ (b → a) :=
⟨λ h, begin
  by_cases A : b,
  simp [A, *] at *,
  simp [A, *] at *,


end,
begin
  intros; split; assumption
end⟩ 

-- so my goal is to define graphs
-- I find the best way to implement them is as a structure with a set of vertices and a binary relation on those vertices
-- I like the coercion from sets to subtypes, but it looks like it makes things a little complicated with the little experience I have (see below)

constants {V : Type} (vertices : set V) (edge : vertices → vertices → Prop)

-- this is an extra convenient definition to allow the creation of "set edges" below
def edges : set (vertices × vertices) := λ ⟨v₁,v₂⟩, edge v₁ v₂

-- I would like to reason on the edge binary relation rather than on the set of edges, that's why I suppose edge is a decidable rel
instance [H : decidable_rel edge] : decidable_pred edges := λ⟨v₁,v₂⟩, H v₁ v₂

-- set of edges whose tip is v ∈ vertices
-- used to define the "in-degree" of vertex v
-- in_edges has type "set edges" because I find it convenient, maybe it's not the best to do (too many coercions ?)
def in_edges (v : vertices) : set edges := let ⟨v,hv⟩ := v in λ⟨⟨_,⟨b,hb⟩⟩, _⟩, b = v

-- I need to use noncomputable because in_edges is a set whose base type is a subtype and
-- I only assume decidable_eq on V
-- but there exists subtype.decidable_eq...
#check subtype.decidable_eq

noncomputable instance [H : decidable_eq V] {v : vertices} : decidable_pred (in_edges v) := let ⟨v,hv⟩ := v in λ⟨⟨⟨a, ha⟩,⟨b,hb⟩⟩, _⟩, H b v
noncomputable instance {v : vertices} [fintype vertices] [decidable_rel edge] [decidable_eq V] : fintype (in_edges v) := @set_fintype _ (set_fintype _) _ _

variables [fintype vertices] [decidable_eq V] [decidable_rel edge]

-- now I want to define some stuff on finite graphs and prove some lemmas
-- for instance, the sum of the in_degrees of all the vertices is equal to fintype.card edges
-- which I did prove, but with another unpleasant setup
noncomputable def in_degree (v : vertices) := finset.card (in_edges v).to_finset
-- this doesn't work without the extra instances above
-- I would like instances to be inferred out-of-the-box but I didn't succeed

#exit
instance : fintype bool2 := bool.fintype

lemma card_bool1 : fintype.card bool2 = 2 :=
begin
  refl,
end

def bool2_fintype : fintype bool2 := ⟨{tt, ff}, λ x, by cases x; simp⟩

def bool2_fintype3 : fintype bool2 := ⟨{ff, tt}, λ x, by cases x; simp⟩

lemma card_bool2 : @fintype.card bool2 bool2_fintype = 2 :=
card_bool1 -- They are defeq

lemma card_bool3 : @fintype.card bool2 bool2_fintype = 2 :=
begin
  rw card_bool1, --doesn't work
end

lemma card_bool4 : @fintype.card bool2 bool2_fintype3 = 2 := card_bool1

#exit
#print rat.has_mul
def poly := list znum

def poly.is_eq_aux : list znum -> list znum -> bool
| [] [] := tt
| [] (h₂ :: t₂) := if (h₂ = 0) then poly.is_eq_aux [] t₂ else ff
| (h₁ :: t₁) [] := if (h₁ = 0) then poly.is_eq_aux t₁ [] else ff
| (h₁ :: t₁) (h₂ :: t₂) := if (h₁ = h₂) then poly.is_eq_aux t₁ t₂ else ff

def poly.is_eq : poly → poly → bool
| [] [] := tt
| [] (h₂ :: t₂) := if (h₂ = 0) then poly.is_eq [] t₂ else ff
| (h₁ :: t₁) [] := if (h₁ = 0) then poly.is_eq t₁ [] else ff
| (h₁ :: t₁) (h₂ :: t₂) := if (h₁ = h₂) then poly.is_eq t₁ t₂ else ff

#print default.sizeof

example (n : ℕ) : n ^ (n + 1) = sorry :=
begin
  simp [nat.pow_succ],
end

def normalizer (H : set G) : set G :=
{ g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H }

instance (H : set G) [is_subgroup H] : is_subgroup (normalizer H) :=
{ one_mem := show ∀ n : G, n ∈ H ↔ 1 * n * 1⁻¹ ∈ H, by simp,
  mul_mem := λ a b (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H)
    (hb : ∀ n, n ∈ H ↔ b * n * b⁻¹ ∈ H) n,
    by rw [mul_inv_rev, ← mul_assoc, mul_assoc a, mul_assoc a, ← ha, hb],
  inv_mem := λ a (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) n,
    by rw [ha (a⁻¹ * n * a⁻¹⁻¹)];
    simp [mul_assoc] }

lemma subset_normalizer (H : set G) [is_subgroup H] : H ⊆ normalizer H :=
λ g hg n, by rw [is_subgroup.mul_mem_cancel_left _ ((is_subgroup.inv_mem_iff _).2 hg),
  is_subgroup.mul_mem_cancel_right _ hg]

instance (H : set G) [is_subgroup H] : normal_subgroup {x : normalizer H | ↑x ∈ H} :=
{ one_mem := show (1 : G) ∈ H, from is_submonoid.one_mem _,
  mul_mem := λ a b ha hb, show (a * b : G) ∈ H, from is_submonoid.mul_mem ha hb,
  inv_mem := λ a ha, show (a⁻¹ : G) ∈ H, from is_subgroup.inv_mem ha, 
  normal := λ a ha ⟨m, hm⟩, (hm a).1 ha }

local attribute [instance] left_rel normal_subgroup.to_is_subgroup

instance : group (left_cosets H) :=
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


variables {I : Type*} (f : I → Type*)
open real 
example : (sqrt 2 + sqrt 3) ^ 2 = 5 + 2 * sqrt 6 :=
begin
  rw [pow_two, mul_add, add_mul, add_mul, ← pow_two, ← pow_two, sqr_sqrt, sqr_sqrt,
    ← sqrt_mul, ← sqrt_mul],
    ring,
end

lemma g : 0.71 + 0.8 = 0.51 := rfl
#print g

example : (ℕ → fin 0) → false := λ f, nat.not_lt_zero (f 0).1 (f 0).2

instance semigroup1 [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
{ mul := begin intros, admit end,
mul_assoc := sorry
}

variables {α : Type*} {β : Type*}
noncomputable theory

namespace finset

lemma image_const [decidable_eq β] {s : finset α} (h : s ≠ ∅) (b : β) : s.image (λa, b) = singleton b :=
ext.2 $ assume b', by simp [exists_mem_of_ne_empty h, eq_comm]

@[simp] theorem max_singleton' [decidable_linear_order α] {a : α} : finset.max (singleton a) = some a :=
max_singleton

section Max
open option

variables [decidable_linear_order β] [inhabited β] {s : finset α} {f : α → β}

def maxi [decidable_linear_order β] [inhabited β] (s : finset α) (f : α → β) : β :=
(s.image f).max.iget

@[simp] lemma maxi_empty : (∅ : finset α).maxi f = default β := rfl

lemma maxi_mem (f : α → β) (h : s ≠ ∅) : s.maxi f ∈ s.image f :=
let ⟨a, ha⟩ := exists_mem_of_ne_empty h in
mem_of_max $ (iget_mem $ is_some_iff_exists.2 $ max_of_mem (mem_image_of_mem f ha))

lemma maxi_le {b : β} (hf : ∀a∈s, f a ≤ b) (hd : s = ∅ → default β ≤ b) : s.maxi f ≤ b :=
classical.by_cases
  (assume h : s = ∅, by simp * at * )
  (assume h : s ≠ ∅,
    let ⟨a, ha, eq⟩ := mem_image.1 $ maxi_mem f h in
    eq ▸ hf a ha)

lemma le_maxi {a : α} (h : a ∈ s) : f a ≤ s.maxi f :=
le_max_of_mem (mem_image_of_mem f h) (iget_mem $ is_some_iff_exists.2 $ max_of_mem (mem_image_of_mem f h))

lemma le_maxi_of_forall {b : β} (hb : ∀a∈s, b ≤ f a) (hd : s = ∅ → b ≤ default β) : b ≤ s.maxi f :=
classical.by_cases
  (assume h : s = ∅, by simp * at * )
  (assume h : s ≠ ∅,
    let ⟨a, ha, eq⟩ := mem_image.1 $ maxi_mem f h in
    eq ▸ hb a ha)

@[simp] lemma maxi_const {b : β} (h : s = ∅ → b = default β) : s.maxi (λa, b) = b :=
classical.by_cases
  (assume h : s = ∅, by simp * at * )
  (assume h, by simp [maxi, image_const h])

end Max

end finset

@[simp] lemma real.default_eq : default ℝ = 0 :=
rfl

namespace metric_space
open finset

instance fintype_function {α : β → Type*} [fintype β] [∀b, metric_space (α b)] :
  metric_space (Πb, α b) :=
{ dist := λf g, maxi univ (λb, _root_.dist (f b) (g b)),
  dist_self := assume f, by simp,
  dist_comm := assume f g, by congr; funext b; exact dist_comm _ _,
  dist_triangle := assume f g h, maxi_le
    (assume b hb,
      calc dist (f b) (h b) ≤ dist (f b) (g b) + dist (g b) (h b) : dist_triangle _ _ _
        ... ≤ maxi univ (λb, _root_.dist (f b) (g b)) + maxi univ (λb, _root_.dist (g b) (h b)) :
          add_le_add (le_maxi hb) (le_maxi hb))
    (by simp [le_refl] {contextual := tt}),
  eq_of_dist_eq_zero := assume f g eq0, funext $ assume b, dist_le_zero.1 $ eq0 ▸
    show dist (f b) (g b) ≤ maxi univ (λb, dist (f b) (g b)), from le_maxi (mem_univ b) }

#print axioms metric_space.fintype_function

end metric_space



#check (cardinal.{0})
#eval (∅ : finset ℕ).sup nat.succ

lemma h {α : Type*} (U : set α) : id '' U = U := by finish [set.image]
#print h

open nat int
lemma nat.mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := 
by induction n; simp [*, nat.pow_succ, mul_comm, mul_assoc, mul_left_comm]

lemma nat.dvd_of_pow_dvd_pow : ∀ {a b n : ℕ}, 0 < n → a ^ n ∣ b ^ n → a ∣ b 
| a 0     := λ n hn h, dvd_zero _
| a (b+1) := λ n hn h, 
let d := nat.gcd a (b + 1) in
have hd : nat.gcd a (b + 1) = d := rfl,
  match d, hd with
  | 0 := λ hd, (eq_zero_of_gcd_eq_zero_right hd).symm ▸ dvd_zero _
  | 1 := λ hd, 
    begin
      have h₁ : a ^ n = 1 := coprime.eq_one_of_dvd (coprime.pow n n hd) h,
      have := pow_dvd_pow a hn,
      rw [nat.pow_one, h₁] at this,
      exact dvd.trans this (one_dvd _),
    end
  | (d+2) := λ hd, 
    have (b+1) / (d+2) < (b+1) := div_lt_self dec_trivial dec_trivial,
    have ha : a = (d+2) * (a / (d+2)) := 
      by rw [← hd, nat.mul_div_cancel' (gcd_dvd_left _ _)],
    have hb : (b+1) = (d+2) * ((b+1) / (d+2)) := 
      by rw [← hd, nat.mul_div_cancel' (gcd_dvd_right _ _)],
    have a / (d+2) ∣ (b+1) / (d+2) := nat.dvd_of_pow_dvd_pow hn $ dvd_of_mul_dvd_mul_left
      (show (d + 2) ^ n > 0, from pos_pow_of_pos _ (dec_trivial))
      (by rwa [← nat.mul_pow, ← nat.mul_pow, ← ha, ← hb]),
    by rw [ha, hb];
      exact mul_dvd_mul_left _ this
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.snd⟩]}

lemma int.nat_abs_pow (a : ℤ) (n : ℕ) : a.nat_abs ^ n = (a ^ n).nat_abs := 
by induction n; simp [*, nat.pow_succ, _root_.pow_succ, nat_abs_mul, mul_comm]

lemma int.dvd_of_pow_dvd_pow {a b : ℤ} {n : ℕ} (hn : 0 < n) (h : a ^ n ∣ b ^ n) : a ∣ b :=
begin
  rw [← nat_abs_dvd, ← dvd_nat_abs, ← int.nat_abs_pow, ← int.nat_abs_pow, int.coe_nat_dvd] at h,
  rw [← nat_abs_dvd, ← dvd_nat_abs, int.coe_nat_dvd],
  exact nat.dvd_of_pow_dvd_pow hn h
end

lemma int.cast_pow {α : Type*} [ring α] (a : ℤ) (n : ℕ) : ((a ^ n : ℤ) : α) = (a : α) ^ n :=
by induction n; simp [*, _root_.pow_succ]

def nth_root_irrational {x : ℤ} {a : ℚ} {n : ℕ} (hn : 0 < n) (h : a ^ n = x) : {a' : ℤ // a = a'} :=
have had : ((a.denom : ℤ) : ℚ) ≠ 0 := int.cast_ne_zero.2 (ne_of_lt (int.coe_nat_lt.2 a.3)).symm,
⟨a.num,
begin 
  rw [rat.num_denom a, rat.mk_eq_div, div_pow _ had, div_eq_iff_mul_eq (pow_ne_zero _ had),
    ← int.cast_pow, ← int.cast_mul, ← int.cast_pow, int.cast_inj] at h,
  have := int.coe_nat_dvd.1 (dvd_nat_abs.2 (int.dvd_of_pow_dvd_pow hn (dvd_of_mul_left_eq _ h))),
  have := coprime.eq_one_of_dvd a.4.symm this,
  rw [rat.num_denom a, rat.mk_eq_div, this],
  simp,
end⟩

instance : euclidean_domain ℤ := 
{ quotient := (/),
  remainder := (%),
  quotient_mul_add_remainder_eq := λ a b,
    by rw [mul_comm, add_comm, int.mod_add_div],
  valuation := int.nat_abs,
  valuation_remainder_lt := λ a b hb, int.coe_nat_lt.1 
    (by rw [← abs_eq_nat_abs b, nat_abs_of_nonneg (mod_nonneg _ hb)]; exact int.mod_lt a hb),
  le_valuation_mul := λ a b hb, by rw nat_abs_mul; 
    exact le_mul_of_ge_one_right' (nat.zero_le _) 
      (nat.pos_of_ne_zero (λ h, hb (eq_zero_of_nat_abs_eq_zero h))) }
#exit
def is_isom (G H : Σ α : Type*, group α) := nonempty (isom G H)

def lift_from {α β γ : Type*} (e : α ≃ β) (f : α → γ) (b : β) : γ := f (e.inv_fun b)

def lift_to {α β γ : Type*} (e : α ≃ β) (f : γ → α) (g : γ) : β := e (f g)

def lift_to_from {α β γ : Type*} (e : α ≃ β) (f : α → α) (b : β) : β := lift_from 

class isom 

def ring_of_ring_of_equiv (α β : Type*) [ring α] (e : α ≃ β) : ring β := 
{ mul := λ a b, e (e.inv_fun a * e.inv_fun b),
  mul_assoc := λ a b c, begin unfold_coes, rw [e.left_inv, e.left_inv, mul_assoc], end

}

theorem canonical_iso_is_canonical_hom {R : Type u} [comm_ring R] {f g : R} (H : Spec.D' g ⊆ Spec.D' f) :
let gbar := of_comm_ring R (powers f) g in
let sα : R → loc (away f) (powers gbar) :=
  of_comm_ring (away f) (powers gbar) ∘ of_comm_ring R (powers f) in
let sγ := (of_comm_ring R (non_zero_on_U (Spec.D' g))) in
by letI H2 := (canonical_iso H).is_ring_hom;
letI H3 : is_ring_hom sα := by apply_instance;
letI H4 : is_ring_hom sγ := by apply_instance; exact
@is_unique_R_alg_hom _ _ _ _ _ _ sγ sα (canonical_iso H).to_fun H4 H3 H2 :=

def disjoint {α β : Type*} [has_mem α β] (s t : β) := ∀ ⦃a : α⦄, a ∈ s → a ∈ t → false

def disjoint1 {α β : Type*} [has_mem α β] (s t : β) := ∀ ⦃a : α⦄, a ∈ s → a ∈ t → false
def add (n m : ℕ) : ℕ := nat.rec n (λ n, nat.succ) m

#eval add 34 3

example (X : Type) (R : Type) (D : R → set X) (γ : Type) (f : γ → R) :
  ⋃₀(D '' set.range f) = ⋃ (i : γ), D (f i) := set.ext (λ x, begin
rw set.sUnion_image, simp, 
end)

theorem mk_eq : ∀ {a b c d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0),
  a /. b = c /. d ↔ a * d = c * b :=
suffices ∀ a b c d hb hd, mk_pnat a ⟨b, hb⟩ = mk_pnat c ⟨d, hd⟩ ↔ a * d = c * b,
[...]

example {p q t : ℕ+} {xp xq : ℤ} {m n : ℕ} (hm : (t : ℕ) = ↑p * m) (hn : (t : ℕ) = ↑q * n) 
    (hpqt : xp * m = xq * n) : xp * q = xq * p :=
have hm0 : (m : ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ h, lt_irrefl (0 : ℕ) (trans_rel_left 
    (<) t.2 (by rwa [h, mul_zero] at hm))),
have hm' : (t : ℤ) = p * m := show ((t : ℕ) : ℤ) = p * m, from hm.symm ▸ by simp,
have hn' : (t : ℤ) = q * n := show ((t : ℕ) : ℤ) = q * n, from hn.symm ▸ by simp,
(domain.mul_right_inj hm0).1 
  (by rw [mul_assoc xq, ← hm', hn', mul_left_comm, ← hpqt, mul_left_comm, mul_assoc])

inductive natε : Type
| ofnat : ℕ → natε 
| addε : ℕ → natε

open natε

def add : natε → natε → natε
| (ofnat a) (ofnat b) := ofnat (a + b)
| (ofnat a) (addε b) := addε (a + b)
| (addε a) (ofnat b) := addε (a + b)
| (addε a) (addε b) := addε (a + b)



instance : has_add (natε) := ⟨add⟩

instance : add_comm_monoid natε :=
{ add := (+),
  zero := ofnat 0,
  add_assoc := λ a b c, by cases a; cases b; cases c; begin unfold has_add.add add,simp, end


}

example : α ≃ set α → false :=
λ f, function.cantor_surjective f f.bijective.2

lemma infinite_real : ¬ nonempty (fintype ℝ) := λ ⟨h⟩, set.infinite_univ_nat 
(set.finite_of_finite_image 
  (show function.injective (@nat.cast ℝ _ _ _), from λ x y, nat.cast_inj.1) 
  ⟨@set_fintype ℝ h _ (classical.dec_pred _)⟩)

lemma omega_le_real : cardinal.omega ≤ ⟦ℝ⟧ := 
le_of_not_gt (λ h, infinite_real (cardinal.lt_omega_iff_fintype.1 h))

noncomputable def real_equiv_complex : ℝ ≃ ℂ := 
equiv.trans
  (classical.choice (quotient.exact (cardinal.mul_eq_self omega_le_real).symm))
  ⟨λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨_, _⟩, rfl, λ ⟨_, _⟩, rfl⟩
attribute [instance] classical.prop_decidable
theorem cantor_surjective (f : α → α → Prop) : ¬ function.surjective f | h :=
let ⟨D, e⟩ := h (λ a, ¬ f a a) in
(iff_not_self (f D D)).1 (iff_of_eq (congr_fun e D))

#print cantor_surjective
lemma em1 (p : Prop) : p ∨ ¬ p := 
have h : xor (xor true p) p := 
  begin
    unfold xor,
  end,

sorry⟩ 
#print eq.refl
def real_equiv_real_squared : ℝ ≃ (ℝ × ℝ) := 
{ to_fun :=


}

lemma red.trans {L₁ L₂ L₃ : list (α × bool)} (H12 : red L₁ L₂) (H23 : red L₂ L₃) : red L₁ L₃ :=
begin
  induction H23 with L1 L1 L2 L3 x b H ih generalizing L₁,
  case red.refl
  { assumption },
  case red.trans_bnot
  { exact red.trans_bnot (ih H12) }
end

lemma church_rosser {L₁ L₂ L₃ : list (α × bool)} (H12 : red L₁ L₂) (H13: red L₁ L₃) :
  ∃ L₄, red L₂ L₄ ∧ red L₃ L₄ :=
begin
  induction H12 with L1 L1 L2 L3 x1 b1 H1 ih1 generalizing L₃,
  case red.refl
  { exact ⟨L₃, H13, red.refl⟩ },
  case red.trans_bnot
  { specialize ih1 H13,
    rcases ih1 with ⟨L₄, H24, H34⟩,
    revert H24,
    generalize HL23 : L2 ++ (x1, b1) :: (x1, bnot b1) :: L3 = L23,
    intro H24,
    induction H24 with L4 L4 L5 L6 x2 b2 H2 ih2,
    case red.refl
    { subst HL23,
      exact ⟨_, red.refl, red.trans_bnot H34⟩ },
    case red.trans_bnot
    { subst HL23,
      admit } }
end

open equiv 
variables {α : Type*}
#print not_iff
lemma mul_apply (a b : perm α) (x : α) : (a * b) x = (a (b x)) := rfl

@[simp] lemma one_apply (x : α) : (1 : perm α) x = x := rfl

def support (a : perm α) : set α := {x : α | a x ≠ x}
set_option pp.implicit true 
set_option pp.notation false
example (a b n : ℕ) : (a * b)^n = a^n * b^n := begin have end

example (f g : perm α) : support (g * f * g⁻¹) = g '' support f :=
set.ext $ λ y, ⟨λ h : _ ≠ _, ⟨g⁻¹ y, λ h₁, by
  rw [mul_apply, mul_apply, h₁, ← mul_apply, mul_inv_self] at h;
  exact h rfl,
show (g * g⁻¹) y = y, by rw mul_inv_self; refl⟩,
λ ⟨x, (hx : _ ≠ _ ∧ _)⟩, show _ ≠ _, 
begin
  rw [mul_apply, ← hx.2, ← mul_apply, ← mul_apply, mul_assoc, inv_mul_self, mul_one, mul_apply],
  assume h,
  rw (equiv.bijective g).1 h at hx,
  exact hx.1 rfl
end⟩

example (f g : perm α) : {x : X | conj g f x ≠ x} = {b : X | f (g⁻¹ b) ≠ g⁻¹ b}

universes u v l
variables {α : Type u} {β : Type v} {γ : Type*}
example (n : ℕ) (summand : ℕ → ℕ) : finset.sum finset.univ (λ (x : fin (succ n)), summand (x.val)) =
    summand n + finset.sum finset.univ (λ (x : fin n), summand (x.val)) := begin
  rw [← insert_erase (mem_univ (⟨n, lt_succ_self n⟩: fin (succ n))), sum_insert (not_mem_erase _ _)],
  refine congr_arg _ _,
  exact sum_bij (λ ⟨i, hi⟩ h, ⟨i, lt_of_le_of_ne (le_of_lt_succ hi) (fin.vne_of_ne (mem_erase.1 h).1)⟩) (λ _ _, mem_univ _)
  (λ ⟨_, _⟩ _, rfl) (λ ⟨a, _⟩ ⟨b, _⟩ _ _ (h : _), fin.eq_of_veq (show a = b, from fin.veq_of_eq h)) 
  (λ ⟨b, hb⟩ _, ⟨⟨b, lt_succ_of_lt hb⟩, ⟨mem_erase.2 ⟨fin.ne_of_vne (ne_of_lt hb), mem_univ _⟩, rfl⟩⟩)
end
#print num
example : (λ n : ℕ, 0) = (λ n, 0) := begin funext, end

example (n : ℕ) : (range n).sum (λ i, 2 * i + 1) = n * n :=
begin
  induction n with n hi,
  refl,
  rw [range_succ, sum_insert (λ h, lt_irrefl _ (mem_range.1 h)), hi, ← add_one],
  ring,
end

theorem meh {i : ℕ} {n : ℕ} : i < n → i < nat.succ n := λ H, lt.trans H $ nat.lt_succ_self _
#print sum_attach
theorem miracle (f : ℕ → ℕ)
(d : ℕ)
(Hd :
  ∀ (g : fin d → ℕ),
    (∀ (i : fin d), f (i.val) = g i) →
      finset.sum (finset.range d) f = finset.sum finset.univ g)
(g : fin (nat.succ d) → ℕ)
(h : ∀ (i : fin (nat.succ d)), f (i.val) = g i)
: finset.sum (finset.range d) f = finset.sum finset.univ (λ (i : fin d), g ⟨i.val, meh i.is_lt⟩)
:=
let gres : fin d → ℕ := λ (i : fin d), g ⟨i.val, meh i.is_lt⟩ in
by rw Hd gres (λ i, h ⟨i.val, _⟩)
#print miracle
example (n : ℕ) (f : ℕ → ℕ) (g : fin n → ℕ) (h : ∀ i : fin n, f i.1 = g i) :
    (range n).sum f = univ.sum g :=
sum_bij (λ i h, ⟨i, mem_range.1 h⟩) (λ _ _, mem_univ _) (λ a ha, h ⟨a, mem_range.1 ha⟩) 
(λ _ _ _ _, fin.veq_of_eq) (λ ⟨b, hb⟩ _, ⟨b, mem_range.2 hb, rfl⟩)

lemma fin_sum (n : ℕ) (f : ℕ → ℕ) : (range n).sum f = univ.sum (f ∘ @fin.val n) := 
sum_bij (λ i h, fin.mk i (mem_range.1 h)) (λ _ _, mem_univ _) (λ _ _, rfl) (λ _ _ _ _, fin.veq_of_eq) 
(λ ⟨b, hb⟩ _, ⟨b, mem_range.2 hb, rfl⟩)
#print fin_sum
#print fin_sum
#check multiset.pmap_eq_map
example (f : β → α) (g : γ → α) (s : finset γ) 

lemma wilson (p : ℕ) (hp : prime p) : fact (p - 1) ≡ p - 1 [MOD p] :=
begin
  
end

inductive  ev : nat →  Prop
| ev_0 : ev 0
| ev_SS : ∀ n : nat, ev n → ev (n+2)
open ev

lemma ev_one : ¬ ev 1 := λ h, by cases h
#print ev_one
def double (n : ℕ) := n + n

lemma ev_double (n : ℕ) : ev (double n) :=
nat.rec ev_0 (λ n h, show ev (_ + _), from (succ_add (succ n) n).symm ▸ ev_SS _ h) n

example {α : Sort*} {f : perm α} : ∃ g h : perm α, g ∘ g = id ∧ h ∘ h = id ∧ f.1 = g ∘ h := begin


end

inductive P : ℕ → Prop
| intro (n : ℕ) : P n
#print ulift
inductive P1 (n : ℕ) : Prop
| intro : P1

#print P1.rec

#print P.rec

inductive eq2 : α → α → Prop
| refl : ∀ a, eq2 a a

#print eq2.rec
#print nat.div
inductive mystery : Sort u
| A : mystery
| B : mystery
#print mystery.rec
def f (n : ℕ) : P n → ℕ := @P.rec (λ n, ℕ) id n

def bla5d (n : ℕ) : ℕ := P.rec id (P.intro n)

lemma zero_one : P 0 = P 1 := propext ⟨λ _, P.intro 1, λ _, P.intro 0⟩

example : f 0 (P.intro 0) = f 1 (P.intro 1)

#print subtype
#check ℕ → ℤ
lemma succ_inj2 (n m : ℕ) : succ n = succ m → n = m := 
λ h, show natnc (succ n) = natnc (succ m), from eq.rec (eq.refl _) h

lemma succ_addax : ∀ b a : ℕ, succ a + b = succ (a + b) :=
λ a, nat.rec (λ a, eq.refl _) (λ a hi b,
show succ (succ b + a) = succ (succ (b + a)),
from eq.rec (eq.refl _) (hi b)) a

lemma zero_addax : ∀ a : ℕ, 0 + a = a :=
λ b, nat.rec (eq.refl zero) 
(λ c (hc : 0 + c = c), show succ (0 + c) = succ c, 
from @eq.rec _ _ (λ d, succ (0 + c) = succ d)
(show succ (0 + c) = succ (0 + c), from eq.refl _) _ hc) b

lemma add_commax : ∀ a b : ℕ, a + b = b + a := λ a,
nat.rec (λ b, zero_addax b) 
(λ b hi c, show succ b + c = succ (c + b),
from eq.rec (eq.rec (succ_addax c b) (hi c)) (succ_addax c b)) a

#print nat.rec
inductive T : Prop
| mk : T → T
#print nat.strong_rec_on
lemma not_T : ¬T := λ h, T.rec_on h (λ _, id)
#print unit.rec

#print eq.rec
lemma f (n m : ℕ) : n = m → n = m :=
λ h, eq.rec rfl h
#print f
inductive T2
| mk : T2 → T2

example : T2 → false := λ t, T2.rec_on t (λ _, id) 
inductive xnat
| zero : xnat
| succ : xnat → xnat

inductive prod2 (α β : Type*)
| mk (fst : α) (snd : β) : prod2

inductive prod3 (α β : Type*)
| mk (fst : α) (snd : β) : prod3

def prod2.fst (α β : Type*) (x : prod2 α β) : α :=
prod2.rec (λ a _, a) x
#print sum

inductive pint
| one : pint
| d : pint → pint
| da : pint → pint

inductive xnat1
| succ : xnat1 → xnat1
| zero : xnat1
| blah : xnat1 → xnat1

#print xnat1.rec
open pint
#print pint.rec_on

def padd_one : pint → pint 
| one    := d one
| (d m)  := da m
| (da m) := d (padd_one m)

def padd : pint → pint → pint
| one m         := padd_one m
| n one         := padd_one n
| (d n) (d m)   := d (padd n m)
| (d n) (da m)  := da (padd n m)
| (da n) (d m)  := da (padd n m)
| (da n) (da m) := d (padd_one (padd n m))

inductive rel : pint → pint → Prop
| oned : ∀ n : pint, rel one (d n)
| oneda : ∀ n : pint, rel one (da n)

def pintwf : has_well_founded Σ' pint, pint :=
{ r := rel,
  wf := well_founded.intro sorry
}

lemma sizeof_pos : ∀ n : pint, 0 < pint.sizeof n
| one    := dec_trivial
| (d m)  := by unfold pint.sizeof; rw add_comm; exact succ_pos _
| (da m) := by unfold pint.sizeof; rw add_comm; exact succ_pos _

def padd2 : pint → pint → pint
| one one       := d one
| one (d m)     := da m
| one (da m)    := d (padd2 one m)
| (d n) one     := da n
| (d n) (d m)   := d (padd2 n m)
| (d n) (da m)  := da (padd2 n m)
| (da n) one    := d (padd2 n one)
| (da n) (d m)  := da (padd2 n m)
| (da n) (da m) := have h : 0 < pint.sizeof n, from sizeof_pos _,
    d (padd2 one (padd2 n m))

#print nat.below
inductive eq2 (a : ℕ) : ℤ → Prop 
| refl : eq2 2

inductive eq3 : Π {α : Sort u}, α → α → Prop
| refl : ∀ {α : Sort u} (a : α), eq3 a a

inductive bla3 (a : ℕ) : ℤ → Prop
| one : ∀ i : ℤ, bla3 (i + a)
| two : bla3 2
| three : ∀ i : ℤ, i < a → bla3 i

inductive bla4 (a : ℕ) : ℕ → Type
| one : Π n : ℕ, bla4 (a + n)

inductive bla5 : ℕ → Prop
| intro (n : ℕ) : bla5 n
#print bla5.rec

def fb (n : ℕ) : bla5 n → ℕ := @bla5.rec (λ n, ℕ) id n

def bla5d (n : ℕ) : ℕ := bla5.rec id (bla5.intro n)
#eval bla5d 5
#reduce bla5d 5
lemma zero_one : bla5 0 = bla5 1 := propext ⟨λ _, bla5.intro 1, λ _, bla5.intro 0⟩

example : @bla5.rec (λ n, ℕ) id (bla5.intro 0) : ℕ) = bla5.rec id (bla5.intro 1) :=
@eq.drec_on Prop (bla5 1) (λ a b, begin end) (bla5 2) zero_one rfl


axiom bla4.rec2 : ∀ {a : ℕ} {C : ℕ → Sort l}, (∀ (n : ℕ), C (a + n)) → 
    ∀ {b : ℕ}, bla4 a b → C b
#print bla4.rec
axiom bla4_iota {a : ℕ} {C : ℕ → Sort l} (f : Π n, C (a + n)) {b : ℕ} 
 : @bla4.rec a C f b (bla4.one b) = 

#print bla4.rec
#print acc.rec
#print eq
#print eq3
#print eq.rec
#print bla3.rec
#print list.perm.rec
#print psum.rec

lemma bla3.rec2 {a : ℕ} {C : ℤ → Sort l} : (Π i : ℤ, C (i + a)) → C 2 → 
(Π i : ℤ, i < a → C i) → Π i : ℤ, bla3 a i → C i := @bla3.rec a C

#print eq2.rec

universe l
#print nat.no_confusion_type
#print nat.no_confusion
#print nat.succ.inj

#print int.cases_on
#print int.rec_on

lemma no_confusion1 : Π {P : Sort l} {v1 v2 : ℕ}, v1 = v2 → nat.no_confusion_type P v1 v2 :=
assume P v1 v2 h,begin
  rw h,
  induction v2,
  exact id,
  assume h,
  exact h rfl,
end

lemma preod {α β : Type*} (p : α × β) : p = prod.mk p.fst p.snd := 
prod.rec (λ f s, rfl) p
#print sigma.rec
lemma bla (P Q R : Prop) : (P ∧ Q → R) ↔ (P → (Q → R)) :=
iff.intro (λ h hp hq, h (and.intro hp hq)) (λ h hpq, h (and.left hpq) (and.right hpq))
#print bla

lemma succ_inj {n m : ℕ} : nat.succ m = nat.succ n → m = n :=
λ h, nat.no_confusion h id

lemma succ_ne_zero (n : ℕ) : nat.succ n ≠ nat.zero := 
@nat.no_confusion _ (nat.succ n) nat.zero

lemma succ_ne (n : ℕ) : nat.succ n ≠ n :=
nat.rec (succ_ne_zero nat.zero) (λ n h hi, h $ succ_inj hi) n
#print prod
def bool.no_confusion_type1 : Sort l → bool → bool → Sort l :=
λ P v1 v2, bool.rec (bool.rec (P → P) P v2)
(bool.rec P (P → P) v2) v1

lemma prod.mk_inj {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β}
  : (x₁, y₁) = (x₂, y₂) → and (x₁ = x₂) (y₁ = y₂) := 
λ h, ⟨show (x₁, y₁).fst = (x₂, y₂).fst, from eq.rec (eq.refl _) h,
      show (x₁, y₁).snd = (x₂, y₂).snd, from eq.rec (eq.refl _) h⟩
set_option pp.implicit true

example : @bool.no_confusion_type1 = @bool.no_confusion_type := rfl
def f : xnat → bool := λ n, xnat.rec ff (λ n h, bnot h) n

lemma bool.no_confusion1 {v1 v2 : bool} : v1 = v2 → bool.no_confusion_type1 false v1 v2 :=
λ h, eq.rec (bool.rec id id v1) h 

example : tt ≠ ff := bool.no_confusion1

example (n : xnat) : succ n ≠ n := xnat.rec n begin end sorry

axiom em2 (p : Prop) : p ∨ ¬p

lemma choice2 {α : Sort*} : nonempty (nonempty α → α) := 
begin
  have := em2 (nonempty α),
  cases this,
  cases this,
  exact ⟨λ h, this⟩,
  exact ⟨λ h, false.elim (this h)⟩ 
end

inductive acc2 {α : Sort u} (r : α → α → Prop) : α → Prop
| intro (x : α) (h : ∀ y, r y x → acc2 y) : acc2 x
#print prefix acc2
axiom em3 (p : Prop) : decidable p
