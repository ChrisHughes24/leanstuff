import data.setoid

def M : Type := (classical.choice ⟨sigma.mk ℕ nat.monoid⟩).1

noncomputable instance : monoid M := (classical.choice ⟨sigma.mk ℕ nat.monoid⟩).2

inductive monoid_expr (α : Type) : Type
| of (a : α) : monoid_expr
| one {} : monoid_expr
| mul    : monoid_expr → monoid_expr → monoid_expr

open monoid_expr

def eval {α β : Type} [has_mul β] [has_one β] (f : α → β) : monoid_expr α → β
| (of x) := f x
| one := 1
| (mul x y) := eval x * eval y

instance : setoid (monoid_expr M) :=
{ r := λ x y, eval id x = eval id y,
  iseqv := ⟨λ _, rfl, λ _ _, eq.symm, λ _ _ _, eq.trans⟩ }

def M' : Type := @quotient (monoid_expr M) monoid_expr.setoid

instance : monoid M' :=
{ mul := λ x y,
    quotient.lift_on₂' x y (λ x y, ⟦mul x y⟧)
      (λ a₁ a₂ b₁ b₂ (h₁ : _ = _) (h₂ : _ = _),
      quotient.sound $ show _ = _,
        by simp [eval, *]),
  mul_assoc := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quotient.sound (mul_assoc (eval id a) _ _)),
  one := ⟦one⟧,
  one_mul := λ a, quotient.induction_on a
    (λ a, quotient.sound (one_mul (eval id a))),
  mul_one := λ a, quotient.induction_on a
    (λ a, quotient.sound (mul_one (eval id a))) }

#exit
import data.fintype tactic.fin_cases
variables p q : Prop

open classical

example : ¬(p → q) → p ∧ ¬q :=
λ h,
have notq : ¬q, from (λ hq', (h (λ hp, hq'))),
and.intro
(or.elim (em p)
id
(
(λ hnp, _)))
notq


instance decidable_eq_endofunctions {qq : Type} [fintype qq] [decidable_eq qq] :
  decidable_eq (qq → qq) := by apply_instance
inductive nand_expr (n : ℕ) : Type
| false {} : nand_expr
| var (i : fin n) : nand_expr
| nand : nand_expr → nand_expr → nand_expr

{x : A × B | ∃ a : A, X = (a, f a)}

namespace nand_expr

def eval {n : ℕ} : nand_expr n → (fin n → bool) → bool
| false      x := ff
| (var i)    x := x i
| (nand a b) x := !((eval a x) && (eval b x))

lemma surjective_eval : Π {n : ℕ} (f : (fin n → bool) → bool),
  {e : nand_expr n // e.eval = f }
| 0 := λ f, if hf : f fin.elim0 = ff
  then ⟨false, funext $ λ x, hf.symm.trans sorry⟩
  else ⟨nand false false, sorry⟩
| (n+1) := λ f, _

end nand_expr

#exit
import data.set.basic

inductive mynat
| zero : mynat
| succ : mynat → mynat

namespace mynat

def one : mynat := succ zero

def two : mynat := succ one

def add (a b : mynat) : mynat :=
mynat.rec b (λ _, succ) a

lemma one_add_one : add one one = two := eq.refl two

lemma one_add_one' : 1 + 1 = 2 := eq.refl 2

set_option pp.all true
#print one_add_one



set_option pp.all true

#print exampl

constant fintype (α : Type) : Type

attribute [class] fintype

def card (α : Type) [fintype α] : ℕ := sorry

constant fintype_range {α : Type} [fintype α] {p : set α} : fintype ↥p

attribute [instance] fintype_range

instance {α β : Type} [fintype β] (f : β → α) : fintype (set.range f) := sorry

lemma subset_lemma {α : Type} [fintype α] {p : set α} : card p = card p := sorry

example {α β : Type} [fintype α] [fintype β] (f : β → α) :
  card (set.range f) = card (set.range f):=
begin
  rw [subset_lemma], --fails
end

#exit
import system.io

def main : io nat :=
do io.put_str "Hello world", return 1

#exit
import tactic.ring data.complex.basic

example (a b c : ℂ) :
  (a + b + c)^2 + (a + b - c)^2 + (a + c - b)^2 + (b + c - a)^2 =
  (2 * a)^2 + (2 * b)^2 + (2 * c)^2 := by ring


#exit
import logic.basic data.fintype tactic.tauto

def xo (a b : Prop) := ¬(a ↔ b)

lemma xo_assoc_aux1 (a b c : Prop) (h : xo (xo a b) c) : xo a (xo b c) :=
λ h₁,
have h : ¬(¬(¬(b ↔ c) ↔ b) ↔ c),
  from λ h₂,
    h ⟨λ hab, h₂.mp (λ h₃, hab (h₁.trans h₃)),
      λ hc hab, h₂.mpr hc (h₁.symm.trans hab)⟩,
have hnc : ¬ c,
  from λ hc, h ⟨λ _, hc, λ hc hbcb,
    have hnb : ¬ b, from λ hb, hbcb.mpr hb (iff_of_true hb hc),
    hnb (hbcb.mp (λ hbc, hnb (hbc.mpr hc)))⟩,
have h : ¬(¬(b ↔ c) ↔ b),
  from (not_not_not_iff _).1 (λ h₁, h ⟨λ h₂, (h₁ h₂).elim, λ hc, (hnc hc).elim⟩),
have h : ¬ (¬ ¬ b ↔ b),
  from λ hb,
    h ⟨λ h, hb.mp (λ hnb, h (iff_of_false hnb hnc)), λ hb hbc, hnc (hbc.mp hb)⟩,
have hnb : ¬ b,
  from λ hb, h (iff_of_true (λ hnb, hnb hb) hb),
h ⟨λ hnnb, (hnnb hnb).elim, λ hb, (hnb hb).elim⟩
#reduce xo_assoc_aux1
lemma xo_assoc_aux2 (a b c : Prop) : xo (xo a b) c → xo a (xo b c) :=
begin
  dsimp [xo],
  assume h h₁,
  replace h : ¬(¬(¬(b ↔ c) ↔ b) ↔ c),
  { assume h₂,
    apply h,
    split,
    { assume hab : ¬ (a ↔ b),
      apply h₂.mp,
      assume h₃,
      apply hab,
      apply h₁.trans,
      exact h₃ },
    { assume hc : c,
      assume hab : a ↔ b,
      apply h₂.mpr hc,
      apply h₁.symm.trans,
      exact hab } },
  clear h₁ a,
  have hnc : ¬ c,
  { assume hc : c,
    apply h,
    split,
    { exact λ _, hc },
    { assume hc hbcb,
      have hnb : ¬ b,
      { assume hb : b,
        apply hbcb.mpr hb,
        exact iff_of_true hb hc },
      { apply hnb,
        apply hbcb.mp,
        assume hbc,
        apply hnb,
        apply hbc.mpr,
        exact hc } } },
  replace h : ¬(¬¬(¬(b ↔ c) ↔ b)),
  { assume h₁,
    apply h,
    split,
    { assume h₂,
      exact (h₁ h₂).elim },
    { assume hc, exact (hnc hc).elim } },
  replace h := (not_not_not_iff _).1 h,
  replace h : ¬ (¬ ¬ b ↔ b),
  { assume hb,
    apply h,
    split,
    { assume h,
      apply hb.mp,
      assume hnb,
      apply h,
      exact iff_of_false hnb hnc },
    { assume hb hbc,
      apply hnc,
      apply hbc.mp hb } },
  clear hnc c,
  have hnb : ¬ b,
  { assume hb,
    apply h,
    exact iff_of_true (λ hnb, hnb hb) hb },
  apply h,
  exact ⟨λ hnnb, (hnnb hnb).elim, λ hb, (hnb hb).elim⟩
end

#reduce xo_assoc_aux


#print ring
set_option class.instance_max_depth 200
instance : fintype (ring bool) :=
fintype.of_equiv
  (Σ' (add : bool → bool → bool)
      (add_assoc : ∀ a b c, add (add a b) c = add a (add b c))
      (zero : bool)
      (zero_add : ∀ a, add zero a = a)
      (add_zero : ∀ a, add a zero = a)
      (neg : bool → bool)
      (add_left_neg : ∀ a, add (neg a) a = zero)
      (add_comm : ∀ a b, add a b = add b a)
      (mul : bool → bool → bool)
      (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
      (one : bool)
      (one_mul : ∀ a, mul one a = a)
      (mul_one : ∀ a, mul a one = a)
      (left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)),
      ∀ b c a, mul (add b c) a = add (mul b a) (mul c a) )
  { to_fun := λ ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩,
      ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩,
    inv_fun := λ ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩,
      ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩,
    left_inv := λ ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩, rfl,
    right_inv := λ a, by cases a; refl }

#eval fintype.card {op : bool → bool → bool //
  ∀ a b c, op (op a b) c = op a (op b c)}

example : fintype.card (ring bool) = 2 := rfl


local attribute [instance, priority 0] classical.prop_decidable

lemma iff.assoc {a b c : Prop} : ((a ↔ b) ↔ c) ↔ (a ↔ (b ↔ c)) :=
if h : a then by simp [h] else by simp [h, not_iff]

lemma or_iff_distrib_left {a b c : Prop} : (a ∨ (b ↔ c)) ↔ ((a ∨ b) ↔ (a ∨ c)) :=
⟨λ h, by cases h; simp [h], λ h, by by_cases a; simp * at *⟩

lemma or_iff_distrib_right {a b c : Prop} : ((a ↔ b) ∨ c) ↔ ((a ∨ c) ↔ (b ∨ c)) :=
by rw [or_comm, or_iff_distrib_left, or_comm, or_comm c]

instance : discrete_field Prop :=
{ add := (↔),
  mul := (∨),
  add_assoc := λ _ _ _, propext $ iff.assoc,
  zero := true,
  zero_add := λ _, propext $ true_iff _,
  add_zero := λ _, propext $ iff_true _,
  neg := id,
  add_left_neg := λ _, propext $ iff_true_intro iff.rfl,
  add_comm := λ _ _, propext iff.comm,
  mul_assoc := λ _ _ _, propext $ or.assoc,
  one := false,
  one_mul := λ _, propext $ false_or _,
  mul_one := λ _, propext $ or_false _,
  left_distrib := λ _ _ _, propext $ or_iff_distrib_left,
  right_distrib := λ _ _ _, propext $ or_iff_distrib_right,
  mul_comm := λ _ _, propext $ or.comm,
  inv := id,
  zero_ne_one := true_ne_false,
  mul_inv_cancel := λ a ha0, if ha : a
    then (ha0 (eq_true_intro ha)).elim
    else eq_false_intro (λ h, h.elim ha ha),
  inv_mul_cancel := λ a ha0, if ha : a
    then (ha0 (eq_true_intro ha)).elim
    else eq_false_intro (λ h, h.elim ha ha),
  has_decidable_eq := classical.dec_eq _,
  inv_zero := rfl }


variable V : Type

structure toto := (val : list V)

inductive shorter : toto V -> toto V -> Prop
| step : ∀ (z : V) (l : list V), shorter ⟨l⟩ ⟨z::l⟩

lemma shorter_wf : well_founded (shorter V)
    := by { apply well_founded.intro, intro l, cases l with xs,
        induction xs with y ys; apply acc.intro; intros; cases a,
        apply xs_ih }

instance : has_well_founded (toto V) := ⟨shorter V, shorter_wf V⟩
#print int.comm_semiring
def fold : toto V -> Prop
    | ⟨[]⟩    := true
    | ⟨x::xs⟩ := have h : shorter V ⟨xs⟩ ⟨x::xs⟩ := shorter.step x xs,
        fold ⟨xs⟩
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, shorter_wf V⟩],
  dec_tac := `[exact h] }

#exit
import set_theory.ordinal

universe u
noncomputable theory
#print axioms int.comm_ring
example : ((<) : cardinal.{u} → cardinal.{u} → Prop)
  ≼o ((<) : ordinal.{u} → ordinal.{u} → Prop) :=
cardinal.ord.order_embedding

def ordinal.to_cardinal : ordinal.{u} → cardinal.{u}
| o := begin
  have :=


end


example : ((<) : ordinal.{u} → ordinal.{u} → Prop)
  ≼o ((<) : cardinal.{u} → cardinal.{u} → Prop) :=
⟨⟨λ o : ordinal.{u}, well_founded.fix ordinal.wf.{u} begin end o, _⟩, _⟩

#exit
import linear_algebra.basic

set_option pp.implicit true




lemma X {p q : Prop} : (p ↔ ¬q) ↔ ¬(p ↔ q) :=
sorry
#print not_false
example {p : Prop} : p ∨ ¬p :=
((@X (p ∨ ¬p) false).mpr (λ h, h.mp (or.inr (λ hp, h.mp (or.inl hp))))).mpr (λb,b)

example := by library_search

example {α : Type} (s : set α) : s = s ⁻¹' {true} :=
set.ext $ λ x, ⟨λ h, or.inl (eq_true_intro h),
  λ h, h.elim (λ h, h.mpr trivial) false.elim⟩

example {ι : Type} (i : ι) (f : Π (j : subtype (≠ i)), M₁ j.val)

import topology.opens

open topological_space

lemma opens.supr_val {X γ : Type*} [topological_space X] (ι : γ → opens X) :
  (⨆ i, ι i).val = ⨆ i, (ι i).val :=
@galois_connection.l_supr (opens X) (set X) _ _ _ (subtype.val : opens X → set X)
    opens.interior opens.gc _

lemma what_is_this_called {X Y : Type*} [topological_space X] [topological_space Y] {f : X → Y}
  (hf : continuous f) {γ : Type*} (ι : γ → opens Y) :
  (⨆ (j : γ), hf.comap (ι j)).val = ⋃ (j : γ), f ⁻¹' (ι j).val :=
opens.supr_val _

#exit
import algebra.pi_instances

universes u v w

class SemiModule (β : Type v) [add_comm_monoid β]

abbreviation Module (β : Type v) [add_comm_group β] :=
SemiModule β

instance piSemiModule (I : Type w) (f : I → Type u)
  [∀ i, add_comm_monoid $ f i] [∀ i, SemiModule (f i)] :
  SemiModule (Π i : I, f i) := by constructor
set_option pp.implicit true
-- instance piSemiModule' (I : Type w) (f : I → Type u)
--   [∀ i, add_comm_group $ f i] [∀ i, SemiModule (f i)] :
--   SemiModule (Π i : I, f i) := begin

--     apply_instance

--   end

example (I : Type w) (f : I → Type u) [∀ i, add_comm_group $ f i] :
  @pi.add_comm_monoid I f _ = @add_comm_group.to_add_comm_monoid _ _ := rfl
set_option trace.class_instances true
#check piSemiModule _ _
instance piModule (I : Type w) (f : I → Type u)
  [∀ i, add_comm_group $ f i] [∀ i, SemiModule (f i)] : -- changed from Module
  Module (Π i : I, f i) := begin
  delta Module,
  -- ⊢ SemiModule (Π (i : I), f i)
  -- apply piSemiModule I f, -- works
  apply_instance -- still fails
end
/-
@SemiModule (Π (i : I), f i)
  (@pi.add_comm_monoid I (λ (i : I), f i) (λ (i : I), _inst_1 i))

-/
#exit
import ring_theory.integral_closure set_theory.schroeder_bernstein
#print function.embedding.trans
example {R A : Type} [comm_ring A] [comm_ring R] [algebra R A] (S : subalgebra R A)
  {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S := by library_search
open_locale classical
example {α β ι : Type*} [hι : nonempty ι] {S : ι → set α} (f : α → β)
  (hf : function.injective f) : (⨅ i, f '' S i) = f '' (⨅ i, S i) :=
by resetI; rcases hι with ⟨i⟩; exact
  set.ext (λ x, ⟨λ h, by rcases set.mem_Inter.1 h i with ⟨y, hy, rfl⟩;
    exact ⟨y, set.mem_Inter.2 (λ j, by rcases set.mem_Inter.1 h j with ⟨z, hz⟩;
      exact (hf hz.2 ▸ hz.1)), rfl⟩,
  by rintros ⟨y, hy, rfl⟩; exact set.mem_Inter.2 (λ i, set.mem_image_of_mem _
    (set.mem_Inter.1 hy _))⟩)
/-
structure functor (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D] :
  Type (max v₁ v₂ u₁ u₂) :=
(obj       : C → D)
(map       : Π {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y)))
(map_id'   : ∀ (X : C), map (𝟙 X) = 𝟙 (obj X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

infixr ` ⥤ `:26 := functor       -- type as \func --
-/

variables {X : Type*} [topological_space X]

open topological_space

def res_functor {Y₁ Y₂ : set X} (hY : Y₂ ⊆ Y₁) :
    {V : opens X // Y₁ ⊆ V} ⥤ {V : opens X // Y₂ ⊆ V} :=
{ obj := λ V, ⟨V.1, set.subset.trans hY V.2⟩,
  map := λ _ _, id}

example (Y : set X) : res_functor (set.subset.refl Y) = 𝟭 _ :=
begin
  apply category_theory.functor.mk.inj_eq.mpr,
  simp, refl,
end

#exit
import data.nat.prime data.zsqrtd.gaussian_int

inductive W {α : Type*} (β : α → Type*)
| mk (a : α) (b : β a → W) : W

def blah {α : Type*} (β : α → Type*) [Π a, fintype (β a)] : W β → ℕ
| mk a b := begin


end



local notation `ℤ[i]` := gaussian_int
#eval let s := (finset.Ico 20 10000).filter nat.prime in
  ((s.sigma (λ n, (finset.Ico 20 n).filter nat.prime)).filter
  (λ n : Σ n, ℕ, nat.sqrt (n.1^2 - n.2^2) ^ 2 = n.1^2 - n.2^2)).image
  (λ n : Σ n, ℕ, (n.1, n.2, (n.1^2 - n.2^2).factors))
#eval nat.factors (71^2 + 31^2)
#eval (nat.prime 31 : bool)
#eval nat.sqrt(181^2 - 19^2)
#eval nat.factors 180
#eval (180^2 + 19^2 = 181^2 : bool)
#eval (nat.prime 181 : bool)

import tactic.split_ifs

open nat

inductive tree : Type
| lf : tree
| nd : tree -> nat -> tree -> tree

open tree

def fusion : tree -> tree -> tree
| lf t2 := t2
| (nd l1 x1 r1) lf := (nd l1 x1 r1)
| (nd l1 x1 r1) (nd l2 x2 r2) :=
    if x1 <= x2
    then nd (fusion r1 (nd l2 x2 r2)) x1 l1
    else nd (fusion (nd l1 x1 r1) r2) x2 l2

def occ : nat -> tree -> nat
| _ lf := 0
| y (nd g x d) := (occ y g) + (occ y d) + (if x = y then 1 else 0)

theorem q5 : ∀ (x : ℕ) (t1 t2 : tree),
    (occ x (fusion t1 t2)) = (occ x t1) + (occ x t2) :=
begin
    intros x t1 t2,
    induction t1 with g1 x1 d1 _ ih1,
    simp [fusion, occ],
    induction t2 with g2 x2 d2 _ ih2,
    simp [fusion, occ],
    by_cases x1 <= x2,
    simp [fusion, h, occ],
    rw ih1,
    simp [occ, fusion, h],
    simp [occ, fusion, h],
    rw ih2,
    simp [occ, fusion],
end
∀ t2
theorem q5 : ∀ (x : ℕ) (t1 t2 : tree),
    (occ x (fusion t1 t2)) = (occ x t1) + (occ x t2) :=
begin
  intros x t1,
  induction t1 with g1 x1 d1 _ ih1,
  { simp [fusion, occ] },
  { assume t2,
    induction t2 with g2 x2 d2 _ ih2,
    simp [fusion, occ],
    by_cases x1 <= x2,
    { simp [fusion, h, occ, ih1] },
    { simp [occ, fusion, h, ih2] }, },
end

theorem q5 (x : ℕ) : ∀ (t1 t2 : tree),
    (occ x (fusion t1 t2)) = (occ x t1) + (occ x t2)
| lf t2 := by simp [fusion, occ]
| (nd l1 x1 r1) lf := by simp [fusion, occ]
| (nd l1 x1 r1) (nd l2 x2 r2) :=
begin
  simp only [fusion, occ],
  by_cases hx12 : x1 ≤ x2,
  { rw [if_pos hx12],
    simp only [fusion, occ],
    rw q5,
    simp [occ] },
  { rw if_neg hx12,
    simp only [fusion, occ],
    rw q5,
    simp [occ] }
end


#exit
import ring_theory.algebra

example {R : Type*} [comm_ring R] :
  (algebra.to_module : module ℤ R) = add_comm_group.module :=


variable {n : ℕ}
open function nat finset
#print test_bit
def binary (A : finset ℕ) : ℕ := A.sum (λ x, pow 2 x)

def ith_bit (n i : ℕ) := n / 2 ^ i % 2


-- lemma ith_bit_binary (A : finset ℕ) : ∀ i,
--   i ∈ A ↔ ¬ even (binary A / 2 ^ i) :=
-- finset.induction_on A
--   (by simp [binary, ith_bit])
--   (λ a s has ih i,
--     begin
--       dsimp [binary, ith_bit] at *,
--       rw [sum_insert has, mem_insert],
--       have hnm : ∀ {n m}, n < m → 2^n / 2^m = 0,
--         from λ n m h, div_eq_of_lt ((pow_lt_iff_lt_right (le_refl _)).2 h),
--       have hnm' : ∀ {n m : ℕ}, n < m → 2^m % 2^n = 0, from sorry,
--       have h2p : ∀ {n : ℕ}, 0 < 2^n, from sorry,
--       rcases lt_trichotomy i a with hia|rfl|hai,
--       { have : even (2^a / 2^i),
--         { rw [even_div, mod_mul_left_div_self, ← dvd_iff_mod_eq_zero],
--           apply dvd_div_of_mul_dvd,
--           rw [← nat.pow_succ],
--           exact pow_dvd_pow _ hia }, sorry,
--         -- rw [hnm' hia, zero_add, if_neg (not_le_of_gt (mod_lt _ h2p))],
--         -- simp [*, ne_of_lt hia, ih, hnm' hia] with parity_simps
--          }, { sorry },
--       -- { rw [mod_self, zero_add, if_neg (not_le_of_gt (mod_lt _ h2p))],
--       --   simp [nat.div_self (nat.pow_pos h2p _), nat.mod_self] with parity_simps,
--       --   finish },--finish },
--       {
--         -- have : 2 ^ a + sum s (pow 2) % 2 ^ i = (2 ^ a + sum s (pow 2)) % 2 ^ i,
--         --   from begin
--         --     rw [add_mod]

--         --   end,
--         -- rw [hnm hai, mod_eq_of_lt ((pow_lt_iff_lt_right (le_refl _)).2 hai)],
--         rw [even_div],
--         simp [ne_of_gt hai, hnm hai, ih] with parity_simps, },
--     end)

lemma ith_bit_binary (A : finset ℕ) : ∀ i,
  i ∈ A ↔ ¬ even (binary A / 2 ^ i) :=
finset.induction_on A
  (by simp [binary, ith_bit])
  (λ a s has ih i,
    begin
      dsimp [binary, ith_bit] at *,
      rw [sum_insert has, mem_insert,
        nat.add_div (nat.pow_pos (show 0 < 2, from dec_trivial) _)],
      have hnm : ∀ {n m}, n < m → 2^n / 2^m = 0,
        from λ n m h, div_eq_of_lt ((pow_lt_iff_lt_right (le_refl _)).2 h),
      have hnm' : ∀ {n m : ℕ}, n < m → 2^m % 2^n = 0, from sorry,
      have h2p : ∀ {n : ℕ}, 0 < 2^n, from sorry,
      rcases lt_trichotomy i a with hia|rfl|hai,
      { have : even (2^a / 2^i),
        { rw [even_div, mod_mul_left_div_self, ← dvd_iff_mod_eq_zero],
          apply dvd_div_of_mul_dvd,
          rw [← nat.pow_succ],
          exact pow_dvd_pow _ hia },
        rw [hnm' hia, zero_add, if_neg (not_le_of_gt (mod_lt _ h2p))],
        simp [*, ne_of_lt hia, ih, hnm' hia] with parity_simps },
      { rw [mod_self, zero_add, if_neg (not_le_of_gt (mod_lt _ h2p))],
        simp [nat.div_self (nat.pow_pos h2p _), nat.mod_self] with parity_simps,
        finish },--finish },
      { have : (2 ^ a + sum s (pow 2)) % 2 ^ i < 2 ^ a + sum s (pow 2) % 2 ^ i,
          from _,
        rw [hnm hai, mod_eq_of_lt ((pow_lt_iff_lt_right (le_refl _)).2 hai)],

        simp [ne_of_gt hai, hnm hai, ih] with parity_simps, },
    end)

lemma ith_bit_binary (A : finset ℕ) : ∀ i,
  i ∈ A ↔ ith_bit (binary A) i = 1 :=
finset.induction_on A
  (by simp [binary, ith_bit])
  (λ a s has ih i, begin
    dsimp [binary, ith_bit] at *,
    rw [sum_insert has, mem_insert, nat.add_div],
    rcases lt_trichotomy i a with hia|rfl|hai,
    {
      rw [if_neg, add_zero],
       }






  end)

example : function.injective (binary) :=
function.injective_of_has_left_inverse
  ⟨λ n, (range n).filter (λ i, n / 2^i ≠ n / 2^(i+1)),
  λ s, finset.induction_on s
    (by simp [binary]) $
    λ a s has ih, begin
      conv_rhs { rw ← ih },
      ext i,
      simp only [binary, sum_insert has, mem_filter, mem_range,
        mem_insert],
      split,
      { assume h,
         }



    end⟩
-- λ s, finset.induction_on s
--   (λ t h, begin simp [binary] at *, end) $
-- λ a s has ih t h,
-- have hat : binary t = binary (insert a (t.erase a)),
--   from h ▸ congr_arg binary (by finish [finset.ext]),
-- begin
--   rw [erase_in]


-- end

example (m : nat) : 0 * m = 0 :=
begin
  induction m with m ih,
  rw mul_zero,
  rw [nat.mul_succ],


end

lemma z (a b c : ℝ) : a^3 + b^3 + c^3 - 3 * a * b * c =
  1/2 * (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2) := by ring

#print z

#exit
import data.set.basic


example {X : Type} (A B : set X) : A ∩ B = A ∪ B ↔ A = B :=
⟨λ h, set.ext $ λ x,
  ⟨λ hA, set.mem_of_subset_of_mem (set.inter_subset_right A B) (h.symm ▸ or.inl hA),
   λ hB, set.mem_of_subset_of_mem (set.inter_subset_left A B) (h.symm ▸ or.inr hB)⟩,
  by simp {contextual := tt}⟩

#exit
import data.int.basic

#print nat_abs
inductive cool : ℕ → Prop
| cool_2 : cool 2
| cool_5 : cool 5
| cool_sum : ∀ (x y : ℕ), cool x → cool y → cool (x + y)
| cool_prod : ∀ (x y : ℕ), cool x → cool y → cool (x*y)

example : 7 = sorry :=
begin
  dsimp only [bit0, bit1],

end

example : cool 7 := (cool.cool_sum 2 5 cool.cool_2 cool.cool_5 : _)

#exit
import data.polynomial

variables {R : Type*} [comm_ring R]
open polynomial

lemma zzzz {u r : R} {n : ℕ} (hr : r^n = 0) (hu : is_unit u) : is_unit (u + r) :=
have hnegr : (-r)^n = 0, by rw [neg_eq_neg_one_mul, mul_pow, hr, mul_zero],
have (X - C (-r)) ∣ X ^ n, from dvd_iff_is_root.2 (by simp [is_root, hnegr]),
is_unit_of_dvd_unit
  (let ⟨p, hp⟩ := this in ⟨p.eval u, by simpa using congr_arg (eval u) hp⟩)
  (is_unit_pow n hu)

#print acc.intro

#exit
import data.zmod.quadratic_reciprocity

@[simp] lemma list.lex_nil_right (l)

#eval @nat.modeq.chinese_remainder 5 8 rfl 4 7

#eval zmodp.legendre_sym 10 71 (by norm_num)

#eval zmodp.legendre_sym 2 71 (by norm_num)

#eval zmodp.legendre_sym 5 71 (by norm_num)

#eval zmodp.legendre_sym 71 5 (by norm_num)

example {α : Type} [nonempty α] (F G : α → Prop)
  (h : (∃ x, F x) → ∃ x, G x) : ∃ x, F x → G x :=
begin
  resetI,
  classical,
  cases _inst_1 with a,
  rcases classical.em (∃ x, G x) with ⟨x, hx⟩ | hx,
  { exact ⟨x, λ _, hx⟩ },
  { exact ⟨a, λ hF, (not_exists.1 (not_imp_not.2 h hx) a hF).elim ⟩ }
end


def sum' (f : ℕ → ℕ) : ℕ → ℕ
| 0     := 0
| (n+1) := sum' n + f n



#exit
import data.equiv.basic group_theory.perm.sign
#eval nat.choose 8 3
#eval (finset.range (721)).filter (λ x, x ∣ 720 ∧ x % 7 = 1)
#eval ((finset.Ico 1 31).powerset.filter
  (λ s : finset ℕ, s.card = 8 ∧
    ((s.filter (λ s : finset ℕ, s.card = 4)).1.map
    (λ s : finset ℕ, s.1.sum)).nodup)


open equiv equiv.perm
variable {α : Type}

open_locale classical

example (f : perm α) (a b : α) :
  f * swap a b * f⁻¹ = sorry :=
begin
  rw [mul_assoc, swap_mul_eq_mul_swap, inv_inv],
  simp,
end

#exit
inductive tree : Type
| lf : tree
| nd : tree -> nat -> tree -> tree

open tree

def fusion : tree -> tree -> tree
| lf t2 := t2
| t1 lf := t1
| (nd l1 x1 r1) (nd l2 x2 r2) :=
    if x1 ≤ x2
    then nd (fusion r1 (nd l2 x2 r2)) x1 l1
    else nd (fusion (nd l1 x1 r1) r2) x2 l2
-- using_well_founded { rel_tac := λ _ _,
--     `[exact ⟨_, measure_wf (λ t, tree.sizeof t.1 + tree.sizeof t.2)⟩] }

#print fusion._main._pack.equations._eqn_1

theorem fusion_lf : ∀ (t : tree), fusion lf lf = lf :=
λ _, rfl

example  (t : tree) : fusion t lf = lf :=
by cases t; refl
#exit
import data.real.nnreal

#print xor

example : (∀ p q r, xor (xor p q) r ↔ xor p (xor q r)) → ∀ p, p ∨ ¬p :=
λ h p,
((h p p true).1
    (or.inr ⟨trivial, λ h, h.elim (λ h, h.2 h.1) (λ h, h.2 h.1)⟩)).elim
  (λ h, or.inl h.1)
  (λ h, or.inr h.2)

example : (∀ p q, xor p q ↔ (p ∨ q) ∧ ¬(p ∧ q)) :=
λ p q, ⟨λ h, h.elim (λ h, ⟨or.inl h.1, λ h1, h.2 h1.2⟩)
    (λ h, ⟨or.inr h.1, λ h1, h.2 h1.1⟩),
  (λ h, h.1.elim
    (λ hp, or.inl ⟨hp, λ hq, h.2 ⟨hp, hq⟩⟩)
    (λ hq, or.inr ⟨hq, λ hp, h.2 ⟨hp, hq⟩⟩))⟩

example : (∀ p q r, ((p ↔ q) ↔ r) ↔ (p ↔ (q ↔ r))) → ∀ p, p ∨ ¬p :=
λ h p,
  ((h (p ∨ ¬p) false false).1
      ⟨λ h, h.1 (or.inr (λ hp, h.1 (or.inl hp))), false.elim⟩).2
    iff.rfl

inductive pre_free_group (α : Type) : Type
| atom : α → pre_free_group
| one : pre_free_group
| mul : pre_free_group → pre_free_group → pre_free_group
| inv : pre_free_group → pre_free_group

namespace pre_free_group

variable {α : Type}

instance : has_one (pre_free_group α) := ⟨pre_free_group.one _⟩
instance : has_mul (pre_free_group α) := ⟨pre_free_group.mul⟩
instance : has_inv (pre_free_group α) := ⟨pre_free_group.inv⟩

lemma mul_def : (*) = @pre_free_group.mul α := rfl
lemma one_def : 1 = @pre_free_group.one α := rfl
lemma inv_def : has_inv.inv = @pre_free_group.inv α := rfl

inductive rel : Π (a b : pre_free_group α), Prop
| mul_assoc : ∀ a b c, rel ((a * b) * c) (a * (b * c))
| one_mul : ∀ a, rel (1 * a) a
| mul_one : ∀ a, rel (a * 1) a
| mul_left_inv : ∀ a, rel (a⁻¹ * a) 1
| mul_lift : ∀ a b c d, rel a b → rel c d → rel (a * c) (b * d)
| inv_lift : ∀ a b, rel a b → rel (a⁻¹) (b⁻¹)
| refl : ∀ a, rel a a
| symm : ∀ a b, rel a b → rel b a
| trans : ∀ a b c, rel a b → rel b c → rel a c

instance (α : Type) : setoid (pre_free_group α) :=
{ r := rel,
  iseqv := ⟨rel.refl, rel.symm, rel.trans⟩ }

end pre_free_group

def free_group (α : Type) := quotient (pre_free_group.setoid α)

namespace free_group
open pre_free_group

variable {α : Type}

instance : group (free_group α) :=
{ one := ⟦1⟧,
  mul := λ a b, quotient.lift_on₂ a b (λ a b, ⟦a * b⟧)
    (λ a b c d h₁ h₂, quotient.sound (rel.mul_lift _ _ _ _ h₁ h₂)),
  inv := λ a, quotient.lift_on a (λ a, ⟦a⁻¹⟧)
    (λ a b h, quotient.sound (rel.inv_lift _ _ h)),
  mul_assoc := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quotient.sound (rel.mul_assoc _ _ _)),
  one_mul := λ a, quotient.induction_on a
    (λ a, quotient.sound (rel.one_mul a)),
  mul_one := λ a, quotient.induction_on a
    (λ a, quotient.sound (rel.mul_one a)),
  mul_left_inv := λ a, quotient.induction_on a
    (λ a, quotient.sound (rel.mul_left_inv _)) }

def atom (a : α) : free_group α := ⟦pre_free_group.atom a⟧

variables {G : Type} [group G]

def lift (G : Type) [group G] (f : α → G) : free_group α →* G :=
{ to_fun := λ a, quotient.lift_on a
    (λ a, show G, from pre_free_group.rec_on a f 1 (λ _ _, (*)) (λ _ g, g⁻¹))
    (λ a b h, begin
      dsimp,
      induction h;
      try { dsimp [mul_def, inv_def, one_def] };
      simp [mul_assoc, *] at *,
    end),
  map_one' := rfl,
  map_mul' := λ a b, quotient.induction_on₂ a b (λ _ _, rfl) }

lemma one_def : (1 : free_group α) = ⟦pre_free_group.one α⟧ := rfl
lemma mul_def {a b : pre_free_group α} :
  @eq (free_group α) ⟦pre_free_group.mul a b⟧ (⟦a⟧ * ⟦b⟧) := rfl
lemma inv_def {a : pre_free_group α} :
  @eq (free_group α) ⟦pre_free_group.inv a⟧ (⟦a⟧⁻¹) := rfl

@[simp] lemma mk_apply {α β : Type*} [monoid α] [monoid β] (f : α → β) (h₁ h₂) (a : α) :
  monoid_hom.mk f h₁ h₂ a = f a := rfl

@[simp] lemma lift_atom (f : α → G) (a : α) : lift G f (atom a) = f a := rfl

lemma lift_unique (f : α → G) (φ : free_group α →* G) (h : ∀ a, φ (atom a) = f a)
  (g : free_group α) : φ g = lift G f g :=
quotient.induction_on g
  (λ a, begin
    dsimp [atom, lift] at *,
    induction a;
    simp [*, one_def.symm, mul_def, inv_def] at *;
    refl,
  end)

end free_group

#exit
import algebra.free

universe u

inductive pre_free_ring (α : Type u) : Type u
| atom : α → pre_free_ring
| zero : pre_free_ring
| one : pre_free_ring
| neg : pre_free_ring → pre_free_ring
| mul : pre_free_ring → pre_free_ring → pre_free_ring
| add : pre_free_ring → pre_free_ring → pre_free_ring

namespace pre_free_ring

variable {α : Type u}

instance : has_zero (pre_free_ring α) := ⟨pre_free_ring.zero _⟩
instance : has_one (pre_free_ring α) := ⟨pre_free_ring.one _⟩
instance : has_neg (pre_free_ring α) := ⟨pre_free_ring.neg⟩
instance : has_mul (pre_free_ring α) := ⟨pre_free_ring.mul⟩
instance : has_add (pre_free_ring α) := ⟨pre_free_ring.add⟩

inductive rel : Π (a b : pre_free_ring α), Prop
| add_assoc : ∀ a b c, rel (a + b + c) (a + (b + c))
| zero_add : ∀ a, rel (0 + a) a
| add_zero : ∀ a, rel (a + 0) a
| add_left_neg : ∀ a, rel (-a + a) 0
| add_comm : ∀ a b, rel (a + b) (b + a)
| mul_assoc : ∀ a b c, rel (a * b * c) (a * (b * c))
| one_mul : ∀ a, rel (1 * a) a
| mul_one : ∀ a, rel (a * 1) a
| left_distrib : ∀ a b c, rel (a * (b + c)) (a * b + a * c)
| right_distrib : ∀ a b c, rel ((a + b) * c) (a * c + b * c)
| add_lift : ∀ a b c d, rel a b → rel c d → rel (a + c) (b + d)
| mul_lift : ∀ a b c d, rel a b → rel c d → rel (a * c) (b * d)
| neg_lift : ∀ a b, rel a b → rel (-a) (-b)
| refl : ∀ a, rel a a
| symm : ∀ a b, rel a b → rel b a
| trans : ∀ a b c, rel a b → rel b c → rel a c

instance (α : Type u) : setoid (pre_free_ring α) :=
{ r := rel,
  iseqv := ⟨rel.refl, rel.symm, rel.trans⟩ }

end pre_free_ring

variable {α : Type u}

def free_ring (α : Type u) := quotient (pre_free_ring.setoid α)

namespace free_ring

open pre_free_ring

instance : ring (free_ring α) :=
{ zero := quotient.mk' 0,
  one := quotient.mk' 1,
  add := λ a b, quotient.lift_on₂ a b (λ a b, quotient.mk (a + b))
    (λ a b c d h₁ h₂, quot.sound (rel.add_lift _ _ _ _ h₁ h₂)),
  mul := λ a b, quotient.lift_on₂ a b (λ a b, quotient.mk (a * b))
    (λ a b c d h₁ h₂, quot.sound (rel.mul_lift _ _ _ _ h₁ h₂)),
  add_assoc := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quot.sound (rel.add_assoc _ _ _)),
  mul_assoc := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quot.sound (rel.mul_assoc _ _ _)),
  zero_add := λ a, quotient.induction_on a (λ a, quot.sound (rel.zero_add a)),
  add_zero := λ a, quotient.induction_on a (λ a, quot.sound (rel.add_zero a)),
  neg := λ a, quotient.lift_on a (λ a, quotient.mk (-a))
    (λ a b h, quot.sound (rel.neg_lift _ _ h)),
  add_left_neg := λ a, quotient.induction_on a
    (λ a, quot.sound (rel.add_left_neg _)),
  add_comm := λ a b, quotient.induction_on₂ a b
    (λ a b, quotient.sound (rel.add_comm _ _)),
  one_mul := λ a, quotient.induction_on a (λ a, quot.sound (rel.one_mul a)),
  mul_one := λ a, quotient.induction_on a (λ a, quot.sound (rel.mul_one a)),
  left_distrib := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quot.sound (rel.left_distrib _ _ _)),
  right_distrib := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quot.sound (rel.right_distrib _ _ _)) }

def atom : α → free_ring α := λ a, ⟦atom a⟧

#print linear_ordered_ring
#print
inductive le : free_ring bool → free_ring bool → Prop
| atom : le (atom ff) (atom tt)
| refl : ∀ x, le x x
| trans : ∀ a b c, le a b → le b c → le a c
| add_le_add_left :


#exit
import group_theory.subgroup algebra.commute

lemma X {α : Type} {φ : α → Prop}: (¬ ∃ v, φ v) ↔ (∀ v, ¬ φ v) :=
⟨λ ex v hv, ex ⟨v, hv⟩, Exists.rec⟩

#exit

open equiv
variables {G : Type*} [group G]
#print equiv.ext
def L (g : G) : perm G := ⟨λ h, g * h, λ h, g⁻¹ * h, λ _, by simp, λ _, by simp⟩

def R (g : G) : perm G := ⟨λ h, h * g⁻¹, λ h, h * g, λ _, by simp, λ _, by simp⟩

lemma perm.ext_iff {f g : perm G} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, by rw h, equiv.perm.ext _ _⟩

lemma forall_mem_range {α β : Type*} {p : β → Prop} {f : α → β} :
  (∀ x ∈ set.range f, p x) ↔ (∀ x, p (f x)) :=
⟨λ h x, h _ (set.mem_range_self _), by rintros h x ⟨y, rfl⟩; exact h _⟩

lemma question_4 : set.centralizer (set.range L : set (perm G)) = set.range R :=
calc set.centralizer (set.range L) = { σ  : perm G | ∀ g g₁, σ (g * g₁) = g * σ g₁ } :
  by simp only [set.ext_iff, commute, semiconj_by, set.centralizer, forall_mem_range, perm.ext_iff];
    tauto
... = set.range R : set.ext $ λ f,
  ⟨λ h, ⟨(f 1)⁻¹, perm.ext_iff.2 $ λ x, by dsimp [R]; rw [inv_inv, ← h, mul_one]⟩,
    by rintros ⟨g, rfl⟩; simp [R, mul_assoc]⟩

#print Z
-- set.subset.antisymm
--   (λ f h, ⟨(f 1)⁻¹, perm.ext_iff.2 $ λ x, begin
--     have := h (L (f 1)) (set.mem_range_self _) ,
--     simp [commute, semiconj_by, L, R, perm.ext_iff] at *,


--   end⟩ )
  -- (λ f, by rintros ⟨g, rfl⟩ f ⟨h, rfl⟩;
  --   simp [set.centralizer, L, R, perm.ext_iff, commute, semiconj_by, mul_assoc])



instance : is_subgroup

#exit
import data.complex.basic tactic.norm_num tactic.ring

lemma X (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) =
  (a^2 + 2 * a * b + b^2) * (a + b)^n :=
by simp only [pow_add]; ring
#print X
example (n : nat) (m : int) : 2^(n+1) * m = 2 * 2^n * m :=
by simp only [pow_add]; ring

#eval ((∘) ∘ (∘)) (+) (*) 13 11 20
#eval (∘) ((∘) (+)) (*) 13 11 20
#eval (((∘) (+)) ∘ (*)) 13 11 20
#eval ((∘) (+)) (* 13) 11 20
#eval ((+) ∘ (* 13)) 11 20
#eval (+) (11 * 13) 20
#eval (11 * 13) + 20

example {X Y : Type*} : Π [nonempty X] [nonempty Y], nonempty (X × Y)
| ⟨x⟩ ⟨y⟩ := ⟨(x, y)⟩

#exit
import data.real.basic order.conditionally_complete_lattice
instance : lattice.conditionally_complete_linear_order_bot (with_bot ℝ) :=
by apply_instance

import data.zsqrtd.gaussian_int

#eval ((finset.range 200).filter
  (λ x, ∃ a b : fin (x + 1), a.1^2 + b.1^2 = x)).sort (≤)

₄
notation `ℤ[i]` := gaussian_int

open euclidean_domain
#eval nat.factors (8 * 74 + 2)
#eval gcd (⟨557, 55⟩ : ℤ[i]) 12049
#eval 32 ^ 2 + 105 ^ 2


#exit

import tactic.omega data.nat.modeq

inductive C : Type
| c1 : C
| c2 : C

inductive D : Type
| d1 : D
| d2 : D

def thing1 (c : C) (d : D) : D :=
c.rec
  (_) -- correct "don't know how to synthesize placeholder -- here's a helpful context"
  (_) -- correct

def thing2 (c : C) (d : D) : D :=
C.rec_on c
  (D.rec_on d _ _ )
  (_)

open nat
example (n : fin 70) : n % 7 = (n / 10 + 5 * (n % 10)) % 7 :=
begin
revert n,
exact dec_trivial,

end

example (n : ℤ) (d : ℕ) (h : (2 : ℚ) * (d * d : ℤ) = ((n * n : ℤ) : ℚ)) :
  2 * ((d : ℤ) * (d : ℤ)) = n * n :=
begin
  rw [← @int.cast_inj ℚ],
end

#exit
import analysis.normed_space.basic
open metric
variables
{V : Type*} [normed_group V] [complete_space V] [normed_space ℝ V]

def B' : set V := closed_ball 0 1

example : B' ⊆ ⋃ (a : V) (H : a ∈ (B' : set V)), ball a 0.5 :=
begin
  sorry
end

#exit

theorem add_comm (a b : ℕ) : begin
  apply eq,
  apply ((+) : ℕ → ℕ → ℕ),
  apply a,
  apply b,
  apply ((+) : ℕ → ℕ → ℕ),
  apply b,
  apply a,
end

#exit
import data.fintype

#eval (@finset.univ (fin 100 × fin 100 × fin 100) _).filter
  (λ k : fin 100 × fin 100 × fin 100, (k.1.1 ^ k.2.1.1 + 1) ∣ (k.1.1 + 1 : ℕ)^k.2.2.1
     ∧ k.1.1 > 1 ∧ k.2.1.1 > 1 ∧ k.2.2.1 > 1)

--import data.zmod.basic data.zmod.quadratic_reciprocity

example {k : ℕ+} (h : (3 ^ (2 ^ ((k - 1) : ℕ) : ℕ) :
  zmod (2 ^ (2 ^ (k : ℕ)) + 1)) = -1) : nat.prime (2 ^ (2 ^ (k : ℕ)) + 1) :=
let n : ℕ+ := ⟨3 ^ (2 ^ ((k - 1) : ℕ) : ℕ) + 1, nat.succ_pos _⟩ in
have p3 : nat.prime 3, by norm_num,
have cp3n : nat.coprime 3 n,
  begin
    dsimp [n, nat.coprime],
    erw [nat.gcd_rec, ← zmodp.val_cast_nat p3 (3 ^ 2 ^ (k - 1 : ℕ) + 1)],
    simp [zero_pow (nat.pow_pos (show 0 < 2, from dec_trivial) _)]
  end,
let u3 : units (zmod n) := (@zmod.units_equiv_coprime n).symm ⟨3, sorry⟩ in
have h3 : u3 ^ (n : ℕ) = 1, from _,
begin



end


import data.fintype

variable {α : Type*}

open finset

theorem fintype.card_subtype_lt [fintype α] (p : α → Prop) [decidable_pred p]
  {x : α} (hx : ¬ p x) : fintype.card {x // p x} < fintype.card α :=
by rw [fintype.subtype_card]; exact finset.card_lt_card
  ⟨subset_univ _, classical.not_forall.2 ⟨x, by simp [*, set.mem_def]⟩⟩

#exit
import data.zmod.basic data.polynomial

open polynomial





inductive T : ℕ → Type
| mk : Π (n m : ℕ) (t : T m) (f : Π {n : ℕ}, T n), T n

#print T.rec

set_option trace.simplify.rewrite true





#print X

import data.nat.prime

open nat

lemma min_fac_le_div {n : ℕ} (pos : 0 < n) (np : ¬ prime n) : min_fac n ≤ n / min_fac n :=
match min_fac_dvd n with
| ⟨0, h0⟩     := absurd pos $ by rw [h0, mul_zero]; exact dec_trivial
| ⟨1, h1⟩     := begin
  rw mul_one at h1,
  rw [prime_def_min_fac, not_and_distrib, ← h1, eq_self_iff_true, not_true, or_false, not_le] at np,
  rw [le_antisymm (le_of_lt_succ np) (succ_le_of_lt pos), min_fac_one, nat.div_one]
end
| ⟨(x+2), hx⟩ := begin
  conv_rhs { congr, rw hx },
  rw [nat.mul_div_cancel_left _ (min_fac_pos _)],
  exact min_fac_le_of_dvd dec_trivial ⟨min_fac n, by rwa mul_comm⟩
end



#exit

import tactic.finish

lemma X (p : Prop): ¬(p ↔ ¬ p) := by ifinish
#print X
open multiset function

lemma eq_zero_iff_forall_not_mem {α : Type*} {s : multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
⟨λ h, h.symm ▸ λ _, not_false, eq_zero_of_forall_not_mem⟩

lemma map_eq_map {α β γ : Type*} (f : α → γ) (g : β → γ) {s : multiset α}
  (hs : s.nodup) {t : multiset β} (ht : t.nodup) (i : Πa∈s, β)
  (hi : ∀a ha, i a ha ∈ t) (h : ∀a ha, f a = g (i a ha))
  (i_inj : ∀a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) (i_surj : ∀b∈t, ∃a ha, b = i a ha) :
  s.map f = t.map g :=
have t = s.attach.map (λ x, i x.1 x.2),
  from (nodup_ext ht (nodup_map
      (show injective (λ x : {x // x ∈ s}, i x.1 x.2), from λ x y hxy,
        subtype.eq (i_inj x.1 y.1 x.2 y.2 hxy))
      (nodup_attach.2 hs))).2
    (λ x, by simp only [mem_map, true_and, subtype.exists, eq_comm, mem_attach];
      exact ⟨i_surj _, λ ⟨y, hy⟩, hy.snd.symm ▸ hi _ _⟩),
calc s.map f = s.pmap  (λ x _, f x) (λ _, id) : by rw [pmap_eq_map]
... = s.attach.map (λ x, f x.1) : by rw [pmap_eq_map_attach]
... = t.map g : by rw [this, multiset.map_map]; exact map_congr (λ x _, h _ _)

#exit
import tactic.ring

example (p : ℕ) : p / 2 * (p / 2) + p / 2 * (p / 2) + p % 2 * (p % 2) +
  (2 * (p / 2 * (p / 2)) + 4 * (p / 2) * (p % 2)) =
    (p % 2 + 2 * (p / 2)) * (p % 2 + 2 * (p / 2)) :=
begin
 ring,

end

example (n : ℕ) : n + n = 2 * n := by ring


import data.nat.prime

inductive option' (α : Sort*) : Sort*
| none {} : option'
| some : α → option'

def zmod (n : ℕ) (h : option' n.prime := option'.none) : Type := fin n

#exit
import data.zmod.basic algebra.euclidean_domain

def remainder_aux (a b : ℤ) : ℤ :=
if hb : b = 0 then a
else (a : zmod ⟨b.nat_abs, int.nat_abs_pos_of_ne_zero hb⟩).val_min_abs

def X : euclidean_domain ℤ :=
{ remainder := remainder_aux,
  quotient := λ a b, (a - remainder_aux a b) / b,
  quotient_zero := by simp [remainder_aux],
  quotient_mul_add_remainder_eq := λ a b,
    begin
      rw [remainder_aux, int.mul_div_cancel', sub_add_cancel],
      split_ifs with hb,
      { simp },
      { erw [← int.nat_abs_dvd,
          ← @zmod.eq_zero_iff_dvd_int ⟨b.nat_abs, int.nat_abs_pos_of_ne_zero hb⟩],
        simp }
    end,
  r := λ x y, x.nat_abs < y.nat_abs,
  r_well_founded := measure_wf _,
  remainder_lt := λ a b hb0,
    by rw [remainder_aux, dif_neg hb0];
      exact lt_of_le_of_lt (zmod.nat_abs_val_min_abs_le _) (nat.div_lt_self
        (int.nat_abs_pos_of_ne_zero hb0) dec_trivial),
  mul_left_not_lt := λ a b hb0, not_lt_of_le $
    by rw [int.nat_abs_mul];
      exact le_mul_of_one_le_right' (nat.zero_le _) (int.nat_abs_pos_of_ne_zero hb0) }

#exit
import algebra.field data.rat.basic data.nat.choose

#print axioms add_pow

#print inv_inv'
set_option trace.simplify.rewrite true
example (x : ℚ) : x⁻¹⁻¹ = x := by simp


@[simp] lemma sol_set_simplex (T : tableau m n) (hT : feasible T) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w obj hT).1.sol_set = T.sol_set :=
by simp [sol_set_eq_res_set_inter_dead_set]

import algebra.group_power

example (n : ℕ) (a b : ℤ) : (a * b) ^ n = a ^ n * b ^ n :=
begin
  induction n with n ih,

end

#exit
import data.equiv.basic data.int.basic data.set.intervals

def int.Ico_fin_equiv (a b : ℤ) : set.Ico a b ≃ fin (int.to_nat $ b - a) :=
calc set.Ico a b ≃ set.Ico 0 (b - a) :
  ⟨λ x, ⟨x.1 - a, sub_nonneg.2 x.2.1, add_lt_add_right x.2.2 _⟩,
  λ x, ⟨x.1 + a, le_add_of_nonneg_left x.2.1, lt_sub_iff_add_lt.1 x.2.2⟩,
  λ _, by simp, λ _, by simp⟩
 ... ≃ fin (int.to_nat $ b - a) :
  ⟨λ x, ⟨x.1.to_nat, int.coe_nat_lt.1 $
    by rw [int.to_nat_of_nonneg x.2.1, int.to_nat_of_nonneg (le_trans x.2.1 (le_of_lt x.2.2))];
      exact x.2.2⟩,
  λ x, ⟨x.1, int.coe_nat_nonneg _, begin
    have := int.coe_nat_lt.2 x.2,
    rwa [int.to_nat_of_nonneg] at this,
    cases b - a;
    simp only [int.to_nat, int.coe_nat_lt, nat.not_lt_zero, *] at *
  end⟩,
  λ x, by simp [int.to_nat_of_nonneg x.2.1],
  λ x, by simp⟩

def int.Ioo_fin_equiv (a b : ℤ) : set.Ioo a b ≃ fin (int.to_nat $ b - (a + 1)) :=
calc set.Ioo a b ≃ set.Ico (a + 1) b : equiv.set.of_eq (by simp [set.ext_iff, int.add_one_le_iff])
... ≃ _ : int.Ico_fin_equiv _ _

def int.Ioc_fin_equiv (a b : ℤ) : set.Ioc a b ≃ fin (int.to_nat $ b - a) :=
calc set.Ioc a b ≃ set.Ioo a (b + 1) : equiv.set.of_eq (by simp [set.ext_iff, int.lt_add_one_iff])
... ≃ fin (int.to_nat $ (b + 1) - (a + 1)) : int.Ioo_fin_equiv _ _
... ≃ fin (int.to_nat $ b - a) : ⟨fin.cast (by simp), fin.cast (by simp),
  λ _, fin.eq_of_veq rfl, λ _, fin.eq_of_veq rfl⟩

def int.Icc_fin_equiv (a b : ℤ) : set.Icc a b ≃ fin (int.to_nat $ b + 1 - a) :=
calc set.Icc a b ≃ set.Ico a (b + 1) : equiv.set.of_eq (by simp [set.ext_iff, int.lt_add_one_iff])
... ≃ fin (int.to_nat $ b + 1 - a) : int.Ico_fin_equiv _ _

class good (n : ℕ).

instance good4 : good 4 := good.mk _

local attribute [-pattern] nat.add has_add.add
local attribute [irreducible] has_add.add
local attribute [reducible] nat.mul

example : good (2 + 2) := infer_instance
example : good (2 * 2) := infer_instance
example : good (0 + 4) := infer_instance
#print has_add.add
#print nat.add
#print has_mul.mul
#print nat.mul
#exit
import tactic

inductive next_to : ℤ → ℤ → Prop
| left : ∀ x, next_to x (x + 1)
| right : ∀ x, next_to (x + 1) x

def next_to (a b : ℤ) := ∃ d ∈ ([-1, 1] : list ℤ), a + d = b

lemma next_to.symm {a b : ℤ} (hab : next_to a b) : next_to b a :=
by rcases hab with ⟨x, hx₁, hx₂⟩;
  exact ⟨-x, by simpa [eq_neg_iff_eq_neg, eq_comm, or_comm] using hx₁, by rw ← hx₂; simp⟩

#exit
#print tc
inductive tc' {α : Type*} (r : α → α → Prop) : α → α → Prop
| base : ∀ {x y}, r x y → tc' x y
| base_trans : ∀ {x y z}, r x y → tc' y z → tc' x z

lemma tc'.trans {α : Type*} (r : α → α → Prop) {x y z}
  (hxy : tc' r x y) : tc' r y z → tc' r x z :=
tc'.rec_on hxy (λ _ _, tc'.base_trans)
  (λ x y b hxy hyb ih hbz, tc'.base_trans hxy (ih hbz))


#print tc
#exit
example : (1 : ℕ) = 1 + @has_zero.zero ℕ ⟨1⟩ :=
begin
  rw add_zero,

end

#exit
import data.list.basic

inductive unit2 : Type
| star : unit2

instance : has_repr unit2 := ⟨λ x, "9"⟩

@[instance, priority 10000] def x : has_repr unit := ⟨λ x, punit.rec_on x "1"⟩
set_option profiler true
#eval if (list.range 1000000).sum = 999999 * 500000 then unit2.star else unit2.star

#eval if (list.range 1000000).sum = 999999 * 500000 then () else ()

#exit
import data.list

open list

lemma filter_false' {α : Type*} (l : list α) : l.filter (λ _, false) = [] := filter_false _

example (xs : list ℕ) : xs.filter (λ x, ¬true) = [] :=
by simp only [not_true]; convert filter_false' xs

example (xs : list ℕ) : xs.filter (λ x, ¬true) = [] :=
by simp only [not_true]; rw ← filter_false' xs; congr

#exit
import algebra.big_operators tactic.ring

def ssquares : ℕ → ℕ
| 0     := 0
| (n+1) := (n+1)*(n+1) + (ssquares n)

theorem ssquares_formula (n : ℕ) : 6*(ssquares n) = n*(n+1)*(2*n+1) :=
nat.rec_on n rfl -- trivial base case
(
assume k,
assume h :  6*(ssquares k) = k*(k+1)*(2*k+1),
show 6*(ssquares (k+1)) = (k+1)*((k+1)+1)*(2*(k+1)+1), from
calc
6*(ssquares (k+1)) = 6*((k+1)*(k+1) + (ssquares k)) : rfl
    ... = 6*((k+1)*(k+1)) + k*(k+1)*(2*k+1) : by rw [left_distrib, h]
    ... = _ : by ring)

#exit
import group_theory.abelianization
#print axioms

#print quotient_group._to_additive
open tactic expr

meta def get_macro : expr → list name
| (mvar _ _ e) := get_macro e
| (local_const _ _ _ e) := get_macro e
| (app e₁ e₂)        := get_macro e₁ ++ get_macro e₂
| (lam _ _ e₁ e₂)    := get_macro e₁ ++ get_macro e₂
| (pi _ _ e₁ e₂)     := get_macro e₁ ++ get_macro e₂
| (elet _ e₁ e₂ e₃)   := get_macro e₁ ++ get_macro e₂ ++ get_macro e₃
| (macro m l)      := macro_def_name m :: l.bind get_macro
| _ := []

-- #eval get_macro `()

-- #print declaration.type
-- run_cmd do e ← get_env, let l : list name := environment.fold e []
--   (λ d l, let t := d.type in cond (expr.occurs `(macro_def) t) (d.to_name :: l)  l),
--   trace l, return ()

def repr_aux : name → string
| name.anonymous := "anonymous"
| (name.mk_string s n) := "mk_string " ++ s ++ " (" ++ repr_aux n ++ ")"
| (name.mk_numeral i n) := "mk_numeral " ++ repr i ++ repr_aux n

run_cmd tactic.add_decl (declaration.defn `sorry [] `(nat) `(0)
  (reducibility_hints.opaque) tt)

def X : false := sorry

lemma Y : false := X
#print axioms
#eval (is_sorry `(X)).is_some

run_cmd do d ← get_decl `sorry, trace d.value, return ()

run_cmd do d ← get_decl `X, trace ((get_macro d.value).map repr_aux)
#print macro_def
def X := by tactic.exact $ macro prod.fst [var 0]
#print tactic.exact

#print expr

#exit
import tactic.norm_num

example : ∃ a b c : ℤ, a^3 + b^3 + c^3 = 42 :=
⟨-80538738812075974, 80435758145817515, 12602123297335631, by norm_num⟩

#exit
inductive T : Type
| foo : T → T

def X : T → T := T.foo

set_option trace.compiler.optimize_bytecode true

#eval X

#exit
import data.zsqrtd.gaussian_int data.list.basic

set_option profiler true
#eval (((((list.range 100).product (list.range 10)).product
  ((list.range 10).product (list.range 10))).map
    (λ a : (nat × nat) × (nat × nat),
      (zsqrtd.mk (int.of_nat a.1.1) (int.of_nat a.1.2) : gaussian_int) /
        ⟨int.of_nat a.2.1, int.of_nat a.2.2⟩)).sum
--5.18 seconds to 1.62 ms



#eval euclidean_domain.gcd
  (⟨35,2⟩ : gaussian_int) 15
#exit
import algebra.big_operators

@[inline] def ack : nat → nat → nat
| 0     y     := y+1
| (x+1) 0     := ack x 1
| (x+1) (y+1) := ack x (ack (x+1) y)

def P : ℕ → Prop := λ n, n < 2

instance : decidable_pred P := λ _, nat.decidable_lt _ _

def X (n : ℕ) : ℕ := if P n then 0 else ack 100 100

set_option trace.compiler.code_gen true
#eval if P 0 then 0 else ack 100 100


#exit

import category_theory.category

open category_theory

variables {obj : Type*} [category obj] (X : obj)
#print nat.add
#exit
import data.zmod.basic

theorem test_ind (n : nat) : (3^n -1) % 2 = 0 :=
have (3 : zmod 2) ^ n - 1 = 0, by simp [show (3 : zmod 2) = 1, from rfl],
have h12 : 1 ≤ 3 ^ n, from by rw ← nat.pow_eq_pow; exact one_le_pow_of_one_le dec_trivial _,
(@zmod.eq_iff_modeq_nat 2 (3 ^ n - 1) 0).1 $ by rw [nat.cast_sub]; simpa



theorem test_ind' (n : nat) : (3^n -1) % 2 = 0 :=
nat.rec_on n rfl
  (λ n ih,
    let ⟨a, ha⟩ := (nat.dvd_iff_mod_eq_zero _ _).2 ih in
    _)





#exit
import data.equiv.basic

#print environment.mk_std
#print acc
universe u
variables {α : Type u} (r : α → α → Prop)

inductive acc2 : α → Type u
| intro (x : α) (h : ∀ y, r y x → acc2 y) : acc2 x

def acc_of_acc2 (a : α) : acc2 r a → acc r a :=
λ h, begin
  induction h,
  refine acc.intro _ (λ _ _, _),
  apply h_ih,
  assumption
end

def acc2_of_acc (a : α) : acc r a → acc2 r a :=
λ h, begin
  induction h,
  refine acc2.intro _ (λ _ _, _),
  apply h_ih,
  assumption
end
set_option pp.proofs true
def acc2_equiv_acc (a : α) : acc2 r a ≃ acc r a :=
{ to_fun := acc_of_acc2 _ _,
  inv_fun := acc2_of_acc _ _,
  left_inv := λ h, begin
    induction acc_of_acc2 _ _ h,
    dsimp [acc2_of_acc] at *,
    induction h_1,
    simp,
    simp [ih] at *, end,
  right_inv := λ _, rfl

  end }

#print acc2.rec

#exit
open tactic
run_cmd
  do let e := environment.mk_std 0,
    tactic.trace (repr (environment.is_inductive e `nat))

run_cmd
  do let e := environment.mk_std 0,
    let t := e.fold 0 (λ _, nat.succ) in
    trace (repr t)

run_cmd
  do e ← tactic.get_env,
    tactic.trace (repr (environment.is_inductive e `nat))

#print environment

#print nat

import init.data.nat

#eval 1 + 1

#exit
import data.nat

import algebra.ordered_group

#print nat


open tactic expr declaration lean reducibility_hints
#print unify


def n_id : ℕ → ℕ
| 0 := 0
| (k+1) := k+1

set_option pp.all true

#print n_id -- n_id._main
#print declaration

def reducibility_hints.to_string : Π (h : reducibility_hints), string
| opaque  := "opaque"
| abbrev  := "abbrev"
| (regular n b)  := "regular " ++ repr n ++ " " ++ repr b

meta def get_reducibility_hints : Π (d : declaration), string
| (defn _ _ _ _ h _) := h.to_string
| _ := "none"

def n_id2 := n_id._main

example : n_id = n_id2 := rfl -- succeeds

example : n_id = λ n, n_id n := rfl -- fails

run_cmd tactic.add_decl $ declaration.defn `n_id3 [] `(ℕ → ℕ) `(n_id._main) (regular 5 ff) tt

example : n_id = λ n, n_id3 n := rfl

#eval do t ← get_decl `n_id2, trace $ get_reducibility_hints t

example : n_id = λ n, n_id n := by {dsimp, refl} -- succeeds
-- proof term:
-- @id.{0} (@eq.{1} (nat → nat) n_id (λ (n : nat), n_id n)) (@eq.refl.{1} (nat → nat) n_id)

example : n_id = λ n, n_id n := -- fails
@id.{0} (@eq.{1} (nat → nat) n_id (λ (n : nat), n_id n)) (@eq.refl.{1} (nat → nat) n_id)

example : n_id2 = λ n, n_id2 n := rfl -- succeeds

example : n_id = λ n, n_id2 n := rfl -- succeeds

def nat2 := nat
instance : has_one nat2 := ⟨(0 : ℕ)⟩
example : (0 : ℕ) = (1 : nat2) := rfl

run_cmd do
  let trace_unify (e1 e2 : expr) : tactic unit := (do
    trace $ "try to unify " ++ to_string e1 ++ " with " ++ to_string e2,
    unify e1 e2 transparency.all tt,
    trace $ "unify successful between " ++ to_string e1 ++ " with " ++ to_string e2),
  let c1 : expr tt := const `nat.pred [],
  let c2 : expr tt := const `nat.pred._main [],
  trace_unify c1 c2, -- success
  trace "",
  let eta_nat t := lam `n binder_info.default (const `nat []) $ mk_app t [var 0],
 -- trace_unify (eta_nat c1) (eta_nat c2), -- failure!
  trace_unify `(@has_one.one nat2 _) `(@has_zero.zero ℕ _)

run_cmd tactic.add_decl $ declaration.thm `blah []
  `(@has_one.one nat2 _ = (0 : ℕ)) (pure `(eq.refl (0 : ℕ)))

#print unify
run_cmd tactic.add_decl $ declaration.thm `prod.fst_def []
    `(∀ α β : Type, ∀ x : α × β, x.fst = prod.rec (λ a b, a) x)
    (pure `(λ α β : Type, λ x : α × β, eq.refl x.fst))
#print blah

attribute [_refl_lemma] prod.fst_def

#print prod.fst_def

#print nat.pred
#print nat.pred._main
#print nat.pred.equations._eqn_1

def f : ℕ → ℕ := nat.pred._main

def g : ℕ → ℕ := f

local attribute [reducible] nat.pred

run_cmd tactic.add_decl $ declaration.thm `nat.pred_eq_pred_main []
  `((λ n, nat.pred n) = λ n, nat.pred._main n) (pure `(@rfl _ nat.pred))

example : (λ n, nat.pred n) = (λ n, nat.pred._main n) := eq.refl nat.pred

#exit
import algebra.ordered_ring

#print nonneg_of_mul_nonneg_left
#print nonneg_of_mul_nonneg_right
#print nonpos_of_mul_nonpos_left
#print nonpos_of_mul_nonpos_right
#print pos_of_mul_pos_left
#print pos_of_mul_pos_right
#print neg_of_mul_neg_left
#print neg_of_mul_neg_right
#print declaration

#eval do d ← tactic.get_decl `nat.rec, tactic.trace d.type.to_raw_fmt.to_string, return ()

variables {α : Type*} [linear_ordered_semiring α] {a b c : α}
#print mul_pos_of_neg_of_neg
lemma neg_of_mul_pos_left (h : 0 < a * b) (hb : b ≤ 0) : a < 0 :=
lt_of_not_ge (λ ha, absurd h (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha hb)))

lemma neg_of_mul_pos_right (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
lt_of_not_ge (λ hb, absurd h (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg ha hb)))

lemma pos_of_mul_neg_left (h : a * b < 0) (hb : 0 ≤ b) : 0 < a :=
lt_of_not_ge (λ ha, absurd h (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos _ _)))

lemma nonneg_of_mul_nonpos_left (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
le_of_not_gt (λ ha, absurd h (not_le_of_gt (mul_pos_of_neg_of_neg _  _)))

#exit
import data.nat.basic

local attribute [instance] classical.dec

lemma Q6 (a b : ℕ) (hab : (a * b + 1) ∣ a ^ 2 + b ^ 2) :
  ¬ ∀ k : ℕ, k^2 * (a * b + 1) ≠ a ^ 2 + b ^ 2:=
λ hk,
have h : ∃ a b, (∀ k : ℕ, k^2 * (a * b + 1) ≠ a ^ 2 + b ^ 2) ∧ (a * b + 1) ∣ a ^ 2 + b ^ 2,
  from ⟨a, b, hk, hab⟩,
let i := nat.find h in
let ⟨j, hj⟩ := nat.find_spec h in
let ⟨n, hn⟩ := hj.2 in
let i' := n * j - i in
have hi' : i' < i, from sorry,
nat.find_min h hi' ⟨(j^2 - n) / i, begin



end⟩

#exit
import data.rat.basic

@[simp] lemma int.square_zero {n : ℤ} : n^2 = 0 ↔ n = 0 :=
begin
  rw pow_two,
  split,
  { contrapose!, intro h,
    rcases lt_trichotomy n 0 with H|rfl|H,
    { apply ne_of_gt, exact mul_pos_of_neg_of_neg H H },
    { contradiction },
    { apply ne_of_gt, exact mul_pos H H } },
  { rintro rfl, simp },
end

lemma int.square_pos {n : ℤ} : n^2 > 0 ↔ n ≠ 0 :=
begin
  rw ←not_iff_not, push_neg,
  split,
  { rw ←int.square_zero, intro h, apply le_antisymm h, exact pow_two_nonneg n },
  { rintro rfl, simp [pow_two] }
end

variables {a b : ℤ} (h : a*b + 1 ∣ a^2 + b^2)
include h

lemma nz : a*b + 1 ≠ 0 :=
begin
  cases h with c h,
  contrapose! h,
  simp [h],
  rw [add_eq_zero_iff' (pow_two_nonneg _) (pow_two_nonneg _)],
  rw [int.square_zero, int.square_zero],
  rintro ⟨rfl, rfl⟩,
  simpa using h,
end

lemma q6_aux (a b : ℤ) (n : ℕ) (hn : a^2 + b^2 = n * (a * b + 1)),
  ∃ k : ℤ, a^2 + b^2 = k^2 * (a * b + 1) :=
begin


end

lemma q6 (a b : ℤ) (h : a*b + 1 ∣ a^2 + b^2) :
  ∃ q : ℚ, q^2 = (a^2 + b^2)/(a*b + 1) :=
begin
  cases q6_aux a b h with k hk,
  use k,
  rw_mod_cast hk, rw rat.mk_eq_div,
  simp,
  rw mul_div_cancel,
  norm_cast,
  simpa using nz h,
end

#exit
import data.fintype

instance psigma.fintype {α : Type*} {β : α → Type*} [fintype α] [∀ a, fintype (β a)] :
  fintype (Σ' a, β a) :=
fintype.of_equiv _ (equiv.psigma_equiv_sigma _).symm

instance psigma.fintype_prop_left {α : Prop} {β : α → Type*} [∀ a, fintype (β a)] [decidable α] :
  fintype (Σ' a, β a) :=
if h : α then fintype.of_equiv (β h) ⟨λ x, ⟨h, x⟩, psigma.snd, λ _, rfl, λ ⟨_, _⟩, rfl⟩
else ⟨∅, λ x, h x.1⟩

instance psigma.fintype_prop_right {α : Type*} {β : α → Prop} [∀ a, decidable (β a)] [fintype α] :
  fintype (Σ' a, β a) :=
fintype.of_equiv {a // β a} ⟨λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, rfl, λ ⟨x, y⟩, rfl⟩

instance psigma.fintype_prop_prop {α : Prop} {β : α → Prop} [∀ a, decidable (β a)] [decidable α] :
  fintype (Σ' a, β a) :=
if h : ∃ a, β a then ⟨{⟨h.fst, h.snd⟩}, λ ⟨_, _⟩, by simp⟩ else ⟨∅, λ ⟨x, y⟩, h ⟨x, y⟩⟩

#exit
import order.conditionally_complete_lattice
import data.real.basic

open classical set lattice

variables (Inf_one : real.Inf {(1:ℝ)} = 1)
          (Inf_zero_one : real.Inf {(0:ℝ), (1:ℝ)} = 0)
include Inf_one Inf_zero_one

lemma foo {K : set ℕ} (h : K = {0}) : (⨅ w : ℕ, (⨅ H : w ∈ K, (1:ℝ))) = 0 :=
have Inf_one : real.Inf {(1 : ℝ)} = 1, from
  le_antisymm (real.Inf_le _ ⟨1, by simp {contextual := tt}⟩ (by simp))
    ((real.le_Inf _ ⟨1, set.mem_singleton (1 : ℝ)⟩ ⟨1, by simp {contextual := tt}⟩).2
      (by simp {contextual := tt})),
show real.Inf (range (λ w, real.Inf (range (λ (H : w ∈ K), (1:ℝ))))) = (0:ℝ), from
have h_range : range (λ w, real.Inf (range (λ (H : w ∈ K), (1:ℝ)))) = {(0:ℝ), (1:ℝ)},
begin
  ext, rw mem_range, split,
  rintros ⟨n, rfl⟩,
  by_cases h₂ : n = (0:ℕ),
  have : n ∈ K, finish,
  have : range (λ (H : n ∈ K), (1:ℝ)) = {(1:ℝ)}, ext, finish,
  rw [this, Inf_one], finish,

  have : n ∉ K, finish,
  have : range (λ (H : n ∈ K), (1:ℝ)) = (∅:set ℝ), ext, finish,
  rw this, show lattice.Inf ∅ ∈ {(0:ℝ), (1:ℝ)}, rw real.Inf_empty, finish,

  simp only [mem_singleton_iff, mem_insert_iff, set.insert_of_has_insert],
  intro h, cases h with h h,
  use 0,
  have : range (λ (H : 0 ∈ K), (1:ℝ)) = {1}, ext, finish,
  rw [this, Inf_one], finish,

  use 1,
  have : range (λ (H : 1 ∈ K), (1:ℝ)) = ∅, ext, finish,
  rw this, show lattice.Inf ∅ = x, rw real.Inf_empty, finish
end,
begin
  rw h_range, exact Inf_zero_one
end

lemma foo' {K : set ℕ} (h : K = {0}) : (⨅ w ∈ K, (1:ℝ)) = 1 :=
show lattice.Inf (range (λ w, lattice.Inf (range (λ (H : w ∈ K), (1:ℝ))))) = (1:ℝ),
from
have ∀ w : ℕ, (range (λ (H : w ∈ K), (1:ℝ)))
have (range (λ w, lattice.Inf (range (λ (H : w ∈ K), (1:ℝ))))) = {(1 : ℝ)},
  from begin simp [h, set.ext_iff], end,
begin


end


#exit
import ring_theory.noetherian ring_theory.principal_ideal_domain


example {K : Type*} [discrete_field K] : is_noetherian_ring K := by apply_instance --works
example {K : Type*} [discrete_field K] : is_noetherian K K := by apply_instance
#exit
import algebra.ordered_Ring

lemma int.succ_ne_self (x : ℤ) : x + 1 ≠ x :=
(ne_of_lt (lt_add_one x)).symm

#exit
import algebra.ordered_ring algebra.group_power tactic.ring

variables {R : Type*} [discrete_linear_ordered_field R]

lemma discriminant_le_zero {a b c : R} (h : ∀ x : R,  0 ≤ a*x*x + b*x + c) :
  b*b - 4*a*c ≤ 0 :=
have complete_square : ∀ x, (a * x * x + b * x + c) * 4 * a =
  (2 * a * x + b) ^ 2 - (b * b - 4 * a * c) :=
λ x, by ring,
begin
  rw [sub_nonpos],
  have := h 0,
  simp at this,


end

#exit
set_option old_structure_cmd true

class has_coe_to_fun' (Γ dom cod : Type) :=
( to_fun : Γ → dom → cod )

instance has_coe_to_fun'.has_coe_to_fun (Γ α β : Type) [has_coe_to_fun' Γ α β] :
  has_coe_to_fun Γ := ⟨_, @has_coe_to_fun'.to_fun _ α β _⟩

structure add_group_hom (α β : Type) [add_group α] [add_group β] :=
( to_fun : α → β )
( map_add : ∀ (a b), to_fun (a + b) = to_fun a + to_fun b )

instance add_group_hom.coe_to_fun (α β : Type) [add_group α] [add_group β] :
  has_coe_to_fun' (add_group_hom α β) α β := ⟨add_group_hom.to_fun⟩

structure ring_hom (α β : Type) [ring α] [ring β] extends add_group_hom α β :=
( map_mul : ∀ (a b), to_fun (a * b) = to_fun a * to_fun b )
( map_one : to_fun 1 = 1 )

instance ring_hom.coe_to_fun (α β : Type*) [ring α] [ring β] :
  has_coe_to_fun' (ring_hom α β) α β := ⟨ring_hom.to_fun⟩

class has_map_add (Γ α β : Type) [has_coe_to_fun' Γ α β] [add_group α]
  [add_group β] :=
( map_add : ∀ (f : Γ) (a b : α), f (a + b) = f a + f b )

instance add_group_hom.has_map_add (α β : Type) [add_group α] [add_group β] :
  has_map_add (add_group_hom α β) α β :=
⟨add_group_hom.map_add⟩

instance ring_hom.has_map_add (α β : Type) [ring α] [ring β] : has_map_add (ring_hom α β) α β :=
⟨ring_hom.map_add⟩

attribute [simp] has_map_add.map_add

example (f : ring_hom ℤ ℤ) (a b : ℤ) : f a + f b = f (a + b) :=
begin
 rw has_map_add.map_add ℤ f,

end

#exit
import ring_theory.noetherian ring_theory.principal_ideal_domain

example {K : Type*} [discrete_field K] : is_noetherian_ring K := by apply_instance --works
example {K : Type*} [discrete_field K] : is_noetherian K K := by apply_instance --fails

def S {X Y : Type} (f : X → Y) : X → X → Prop := λ x₁ x₂, f x₁ = f x₂

example {X Y : Type} (f : X → Y) : reflexive (S f) := λ x, rfl -- works
example {X Y : Type} (f : X → Y) : reflexive (S f) := λ x, begin
refl, end -- fails!

#exit

example {R : Type*} [monoid R] {a b c : R} (hab : a * b = 1) (hca : c * a = 1) : b = c :=
by rw [← one_mul b, ← hca, mul_assoc, hab, mul_one]

#exit
import data.real.cardinality group_theory.quotient_group set_theory.ordinal
#print real.topological_space
open cardinal

instance rat_cast_is_add_group_hom : is_add_group_hom (coe : ℚ → ℝ) :=
{ to_is_add_hom := { map_add := by simp } }

instance : is_add_subgroup (set.range (coe : ℚ → ℝ)) :=
is_add_group_hom.range_add_subgroup _

lemma rat_lt_real : mk ℚ < mk ℝ :=
calc mk ℚ = mk ℕ : quotient.sound ⟨denumerable.equiv₂ _ _⟩
... = omega : mk_nat
... < 2 ^ omega.{0} : cantor _
... = mk ℝ : mk_real.symm

lemma omega_eq_set_range_coe : omega.{0} = mk (set.range (coe : ℚ → ℝ)) :=
by rw [← mk_rat]; exact quotient.sound ⟨equiv.set.range _ rat.cast_injective⟩

lemma ne_zero_of_nonempty {α : Type*} [hn : nonempty α] : mk α ≠ 0 :=
λ f, nonempty.elim hn (λ a, pempty.elim (classical.choice (quotient.exact f) a))

noncomputable lemma real_equiv_real_mod_rat : ℝ ≃ quotient_add_group.quotient
  (set.range (coe : ℚ → ℝ)) :=
have ℝ ≃ quotient_add_group.quotient (set.range (coe : ℚ → ℝ)) ×
  (set.range (coe : ℚ → ℝ)) := is_add_subgroup.add_group_equiv_quotient_times_subgroup _,
calc ℝ ≃ quotient_add_group.quotient (set.range (coe : ℚ → ℝ)) ×
  (set.range (coe : ℚ → ℝ)) : is_add_subgroup.add_group_equiv_quotient_times_subgroup _
... ≃ quotient_add_group.quotient (set.range (coe : ℚ → ℝ)) : classical.choice $
  quotient.exact $ show mk _ * mk _ = mk _,
begin
  have hR : cardinal.mk _ = cardinal.mk _ * cardinal.mk _ := quotient.sound ⟨this⟩,
  have hQ :  cardinal.mk ℚ = cardinal.mk (set.range (coe : ℚ → ℝ)),
    from quotient.sound ⟨equiv.set.range _ (λ _, by simp)⟩,
  have : cardinal.mk (set.range (coe : ℚ → ℝ)) <
    cardinal.mk (quotient_add_group.quotient (set.range (coe : ℚ → ℝ))) :=
    begin
      refine lt_of_not_ge _,
      assume h,
      rw [mul_comm, mul_eq_max_of_omega_le_left (le_of_eq omega_eq_set_range_coe)
        (@ne_zero_of_nonempty _ ⟨(0 : quotient_add_group.quotient _)⟩),
        max_eq_left h, ← hQ] at hR,
      exact absurd rat_lt_real (by rw hR; exact lt_irrefl _), apply_instance
    end,
  rw [mul_comm, mul_eq_max_of_omega_le_left (le_of_eq omega_eq_set_range_coe),
    max_eq_right (le_of_lt this)],
  exact (@ne_zero_of_nonempty _ ⟨(0 : quotient_add_group.quotient _)⟩)
end

noncomputable def f : ℝ → ℝ := real_equiv_real_mod_rat.symm ∘ quotient_add_group.mk

lemma thingy_aux (s : set ℝ) (hs : is_open s) (hsn : s ≠ ∅)
  (x : quotient_add_group.quotient (set.range (coe : ℚ → ℝ))) :
  ∃ y ∈ s, quotient_add_group.mk y = x :=
let ⟨a, ha⟩ := set.exists_mem_of_ne_empty hsn in
let ⟨b, hb⟩ := @quotient.exists_rep _ (id _) x in
let ⟨q, hq⟩ := set.exists_mem_of_ne_empty (mem_closure_iff.1
  (dense_inducing.dense dense_embedding_of_rat.to_dense_inducing a) s hs ha) in
let ⟨r, hr⟩ := set.exists_mem_of_ne_empty (mem_closure_iff.1
  (dense_inducing.dense dense_embedding_of_rat.to_dense_inducing (-b))
  ((λ x, b + (x + q)) ⁻¹' s)
   (continuous_add continuous_const
     (continuous_add continuous_id continuous_const) s hs)
   (by rw [set.mem_preimage, add_neg_cancel_left]; exact hq.1)) in
⟨_, hr.1, begin
  rw [← hb],
  refine quotient.sound' _,
  show _ ∈ set.range (coe : ℚ → ℝ),
  simp [-set.mem_range],
  exact is_add_submonoid.add_mem (is_add_subgroup.neg_mem hq.2)
    (is_add_subgroup.neg_mem hr.2)
end⟩

lemma thingy (s : set ℝ) (hs : is_open s) (hsn : s ≠ ∅) (x : ℝ) : ∃ y ∈ s, f y = x :=
let ⟨y, hy⟩ := thingy_aux s hs hsn (real_equiv_real_mod_rat x) in
⟨y, hy.fst, by rw [f, function.comp_app, hy.snd, equiv.symm_apply_apply]⟩

#exit
import data.fintype data.zmod.basic

open finset equiv

example : ∀ {n : ℕ} (g : fin (n + 1) → fin n),
  ∃ (f₁ f₂ : perm (fin (n + 1))), ∀ x, (f₁ x : ℕ) + f₂ x ≡ x [MOD (n+1)]
| 0     g := ⟨1, 1, by simp [nat.modeq]⟩
| (n+1) g := begin



end

#exit
import data.quot logic.basic

meta def choice {α : Sort*} {β : α → Sort*} : (Π a, trunc (β a)) → trunc (Π a, β a) :=
λ f, trunc.mk (λ a, quot.unquot (f a))

def decidable_true (choice : Π {α : Sort*} {β : α → Sort*}
  (f : Π a, trunc (β a)), trunc (Π a, β a)) : decidable true :=
trunc.rec_on_subsingleton (choice (id : trunc bool → trunc bool))
  (λ f, decidable_of_iff (f (trunc.mk tt) = f (trunc.mk ff))
    (by rw [subsingleton.elim (trunc.mk tt) (trunc.mk ff)]; exact eq_self_iff_true _))

#eval decidable_true @choice --ff


def bool_dec_eq_of_choice (choice : Π {α : Sort*} {β : α → Sort*} (f : Π a, trunc (β a)),
  trunc (Π a, β a)) : decidable_eq bool :=
trunc.rec_on_subsingleton (choice (id : trunc bool → trunc bool))
  (λ f a b, decidable_of_iff (f (trunc.mk a) = f (trunc.mk b))
    ⟨_, _⟩)

def choice_computes {α : Sort*} {β : α → Sort*} (f : Π a, trunc (β a)) :
  ∀ a : α, trunc.lift_on (f a) (λ b, trunc.lift_on (choice f) (λ f, f a = b)
    sorry) sorry

example : false :=
begin
  have := choice_computes (id : trunc bool → trunc bool) (trunc.mk tt),

  dsimp [trunc.lift_on, trunc.lift, trunc.mk] at this,


end

section
parameter (p : Prop)

def r : setoid bool :=
  { r := λ x y : bool, p ∨ x = y,
    iseqv := ⟨λ _, or.inr rfl,
      λ x y hxy, hxy.elim or.inl (or.inr ∘ eq.symm),
      λ x y z hxy hyz, hxy.elim or.inl
        (λ hxy, hyz.elim or.inl (λ hyz, or.inr $ by rw [hxy, hyz]))⟩ }

def suspension : Type := quotient r

noncomputable lemma g : trunc (Π s : suspension, {b : bool // @quotient.mk _ r b = s}) :=
choice (λ s, @quotient.rec_on_subsingleton _ (id _)
  (λ t, t = s → trunc {b : bool // @quotient.mk _ r b = s}) _ s
    (λ b hb, trunc.mk ⟨b, hb⟩) rfl)

noncomputable lemma prop_decidable : decidable p :=
trunc.rec_on_subsingleton g
  (λ g', let g := λ s, (g' s).val in
    have quot_mk_g : ∀ s, quotient.mk' (g s) = s, from λ s, (g' s).2,
    have g_injective : function.injective g, from
      function.injective_of_has_left_inverse ⟨_, quot_mk_g⟩,
    have p_iff_g_tt_eq_g_ff : p ↔ g (quotient.mk' tt) = g (quotient.mk' ff),
      from ⟨λ hp, congr_arg _ (quotient.sound' (or.inl hp)),
        λ h, (@quotient.exact _ (id _) _ _ (g_injective h)).elim
          id
          (λ h, bool.no_confusion h)⟩,
    decidable_of_iff _ p_iff_g_tt_eq_g_ff.symm)


#exit
import data.finsupp order.complete_lattice algebra.ordered_group data.mv_polynomial
import algebra.order_functions

namespace multiset
variables {α : Type*} [decidable_eq α]

def to_finsupp (s : multiset α) : α →₀ ℕ :=
{ support := s.to_finset,
  to_fun := λ a, s.count a,
  mem_support_to_fun := λ a,
  begin
    rw mem_to_finset,
    convert not_iff_not_of_iff (count_eq_zero.symm),
    rw not_not
  end }

@[simp] lemma to_finsupp_support (s : multiset α) :
  s.to_finsupp.support = s.to_finset := rfl

@[simp] lemma to_finsupp_apply (s : multiset α) (a : α) :
  s.to_finsupp a = s.count a := rfl

@[simp] lemma to_finsupp_zero :
  to_finsupp (0 : multiset α) = 0 :=
finsupp.ext $ λ a, count_zero a

@[simp] lemma to_finsupp_add (s t : multiset α) :
  to_finsupp (s + t) = to_finsupp s + to_finsupp t :=
finsupp.ext $ λ a, count_add a s t

namespace to_finsupp

instance : is_add_monoid_hom (to_finsupp : multiset α → α →₀ ℕ) :=
{ map_zero := to_finsupp_zero,
  map_add  := to_finsupp_add }

end to_finsupp

@[simp] lemma to_finsupp_to_multiset (s : multiset α) :
  s.to_finsupp.to_multiset = s :=
ext.2 $ λ a, by rw [finsupp.count_to_multiset, to_finsupp_apply]

end multiset

namespace finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ]

instance [preorder α] [has_zero α] : preorder (σ →₀ α) :=
{ le := λ f g, ∀ s, f s ≤ g s,
  le_refl := λ f s, le_refl _,
  le_trans := λ f g h Hfg Hgh s, le_trans (Hfg s) (Hgh s) }

instance [partial_order α] [has_zero α] : partial_order (σ →₀ α) :=
{ le_antisymm := λ f g hfg hgf, finsupp.ext $ λ s, le_antisymm (hfg s) (hgf s),
  .. finsupp.preorder }

instance [ordered_cancel_comm_monoid α] [decidable_eq α] :
  add_left_cancel_semigroup (σ →₀ α) :=
{ add_left_cancel := λ a b c h, finsupp.ext $ λ s,
  by { rw finsupp.ext_iff at h, exact add_left_cancel (h s) },
  .. finsupp.add_monoid }

instance [ordered_cancel_comm_monoid α] [decidable_eq α] :
  add_right_cancel_semigroup (σ →₀ α) :=
{ add_right_cancel := λ a b c h, finsupp.ext $ λ s,
  by { rw finsupp.ext_iff at h, exact add_right_cancel (h s) },
  .. finsupp.add_monoid }

instance [ordered_cancel_comm_monoid α] [decidable_eq α] :
  ordered_cancel_comm_monoid (σ →₀ α) :=
{ add_le_add_left := λ a b h c s, add_le_add_left (h s) (c s),
  le_of_add_le_add_left := λ a b c h s, le_of_add_le_add_left (h s),
  .. finsupp.add_comm_monoid, .. finsupp.partial_order,
  .. finsupp.add_left_cancel_semigroup, .. finsupp.add_right_cancel_semigroup }

attribute [simp] to_multiset_zero to_multiset_add

@[simp] lemma to_multiset_to_finsupp (f : σ →₀ ℕ) :
  f.to_multiset.to_finsupp = f :=
ext $ λ s, by rw [multiset.to_finsupp_apply, count_to_multiset]

def diagonal (f : σ →₀ ℕ) : finset ((σ →₀ ℕ) × (σ →₀ ℕ)) :=
((multiset.diagonal f.to_multiset).map (prod.map multiset.to_finsupp multiset.to_finsupp)).to_finset

lemma mem_diagonal {f : σ →₀ ℕ} {p : (σ →₀ ℕ) × (σ →₀ ℕ)} :
  p ∈ diagonal f ↔ p.1 + p.2 = f :=
begin
  erw [multiset.mem_to_finset, multiset.mem_map],
  split,
  { rintros ⟨⟨a, b⟩, h, rfl⟩,
    rw multiset.mem_diagonal at h,
    simpa using congr_arg multiset.to_finsupp h },
  { intro h,
    refine ⟨⟨p.1.to_multiset, p.2.to_multiset⟩, _, _⟩,
    { simpa using congr_arg to_multiset h },
    { rw [prod.map, to_multiset_to_finsupp, to_multiset_to_finsupp, prod.mk.eta] } }
end

lemma swap_mem_diagonal {n : σ →₀ ℕ} {f} (hf : f ∈ diagonal n) : f.swap ∈ diagonal n :=
by simpa [mem_diagonal, add_comm] using hf

@[simp] lemma diagonal_zero : diagonal (0 : σ →₀ ℕ) = {(0,0)} := rfl

lemma to_multiset_strict_mono : strict_mono (@to_multiset σ _) :=
λ m n h,
begin
  rw lt_iff_le_and_ne at h ⊢, cases h with h₁ h₂,
  split,
  { rw multiset.le_iff_count, intro s, rw [count_to_multiset, count_to_multiset], exact h₁ s },
  { intro H, apply h₂, replace H := congr_arg multiset.to_finsupp H, simpa using H }
end

lemma sum_lt_of_lt (m n : σ →₀ ℕ) (h : m < n) :
  m.sum (λ _, id) < n.sum (λ _, id) :=
begin
  rw [← card_to_multiset, ← card_to_multiset],
  apply multiset.card_lt_of_lt,
  exact to_multiset_strict_mono _ _ h
end

variable (σ)

def lt_wf : well_founded (@has_lt.lt (σ →₀ ℕ) _) :=
subrelation.wf (sum_lt_of_lt) $ inv_image.wf _ nat.lt_wf

-- instance : has_well_founded (σ →₀ ℕ) :=
-- { r := (<),
--   wf := lt_wf σ }

end finsupp

/-- Multivariate power series, where `σ` is the index set of the variables
and `α` is the coefficient ring.-/
def mv_power_series (σ : Type*) (α : Type*) := (σ →₀ ℕ) → α

namespace mv_power_series
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ]

def coeff (n : σ →₀ ℕ) (φ : mv_power_series σ α) := φ n

@[extensionality] lemma ext {φ ψ : mv_power_series σ α} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
funext h

lemma ext_iff {φ ψ : mv_power_series σ α} : φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

variables [comm_semiring α]

def monomial (n : σ →₀ ℕ) (a : α) : mv_power_series σ α := λ m, if m = n then a else 0

lemma coeff_monomial (m n : σ →₀ ℕ) (a : α) :
  coeff m (monomial n a) = if m = n then a else 0 := rfl

@[simp] lemma coeff_monomial' (n : σ →₀ ℕ) (a : α) :
  coeff n (monomial n a) = a := if_pos rfl

def C (a : α) : mv_power_series σ α := monomial 0 a

lemma coeff_C (n : σ →₀ ℕ) (a : α) :
  coeff n (C a : mv_power_series σ α) = if n = 0 then a else 0 := rfl

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a : mv_power_series σ α) = a :=
coeff_monomial' 0 a

@[simp] lemma monomial_zero (a : α) : (monomial 0 a : mv_power_series σ α) = C a := rfl

def X (s : σ) : mv_power_series σ α := monomial (single s 1) 1

lemma coeff_X (n : σ →₀ ℕ) (s : σ) :
  coeff n (X s : mv_power_series σ α) = if n = (single s 1) then 1 else 0 := rfl

lemma coeff_X' (s t : σ) :
  coeff (single t 1) (X s : mv_power_series σ α) = if t = s then 1 else 0 :=
if h : t = s then by simp [h, coeff_X] else
begin
  rw [coeff_X, if_neg h],
  split_ifs with H,
  { have := @finsupp.single_apply σ ℕ _ _ _ t s 1,
    rw [if_neg h, H, finsupp.single_apply, if_pos rfl] at this,
    exfalso, exact one_ne_zero this, },
  { refl }
end

@[simp] lemma coeff_X'' (s : σ) :
  coeff (single s 1) (X s : mv_power_series σ α) = 1 :=
by rw [coeff_X', if_pos rfl]

section ring
variables (σ) (α) (n : σ →₀ ℕ) (φ ψ : mv_power_series σ α)

def zero : mv_power_series σ α := λ n, 0

instance : has_zero (mv_power_series σ α) := ⟨zero σ α⟩

@[simp] lemma coeff_zero : coeff n (0 : mv_power_series σ α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : mv_power_series σ α) = 0 :=
ext $ λ n, if h : n = 0 then by simp [h] else by rw [coeff_C, if_neg h, coeff_zero]

def one : mv_power_series σ α := C 1

instance : has_one (mv_power_series σ α) := ⟨one σ α⟩

@[simp] lemma coeff_one :
  coeff n (1 : mv_power_series σ α) = if n = 0 then 1 else 0 := rfl

@[simp] lemma coeff_one_zero : coeff 0 (1 : mv_power_series σ α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : mv_power_series σ α) = 1 := rfl

def add (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, coeff n φ + coeff n ψ

instance : has_add (mv_power_series σ α) := ⟨add σ α⟩

variables {σ α}

@[simp] lemma coeff_add : coeff n (φ + ψ) = coeff n φ + coeff n ψ := rfl

@[simp] lemma zero_add : (0 : mv_power_series σ α) + φ = φ := ext $ λ n, zero_add _

@[simp] lemma add_zero : φ + 0 = φ := ext $ λ n, add_zero _

lemma add_comm : φ + ψ = ψ + φ := ext $ λ n, add_comm _ _

lemma add_assoc (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ + φ₂) + φ₃ = φ₁ + (φ₂ + φ₃) :=
ext $ λ n, by simp

@[simp] lemma monomial_add (n : σ →₀ ℕ) (a b : α) :
  (monomial n (a + b) : mv_power_series σ α) = monomial n a + monomial n b :=
ext $ λ m, if h : m = n then by simp [h] else by simp [coeff_monomial, if_neg h]

@[simp] lemma C_add (a b : α) : (C (a + b) : mv_power_series σ α) = C a + C b :=
monomial_add 0 a b

variables (σ α)

def mul (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, (finsupp.diagonal n).sum (λ p, coeff p.1 φ * coeff p.2 ψ)
instance : has_mul (mv_power_series σ α) := ⟨mul σ α⟩

variables {σ α}

lemma coeff_mul :
  coeff n (φ * ψ) = (finsupp.diagonal n).sum (λ p, coeff p.1 φ * coeff p.2 ψ) := rfl

@[simp] lemma C_mul (a b : α) : (C (a * b) : mv_power_series σ α) = C a * C b :=
ext $ λ n,
begin
  rw [coeff_C, coeff_mul],
  split_ifs,
  { subst n, erw [diagonal_zero, finset.sum_singleton, coeff_C_zero, coeff_C_zero] },
  { rw finset.sum_eq_zero,
    rintros ⟨i,j⟩ hij,
    rw mem_diagonal at hij, rw [coeff_C, coeff_C],
    split_ifs; try {simp * at *; done} }
end

@[simp] lemma zero_mul : (0 : mv_power_series σ α) * φ = 0 :=
ext $ λ n, by simp [coeff_mul]

@[simp] lemma mul_zero : φ * 0 = 0 :=
ext $ λ n, by simp [coeff_mul]

lemma mul_comm : φ * ψ = ψ * φ :=
ext $ λ n, finset.sum_bij (λ p hp, p.swap)
  (λ p hp, swap_mem_diagonal hp)
  (λ p hp, mul_comm _ _)
  (λ p q hp hq H, by simpa using congr_arg prod.swap H)
  (λ p hp, ⟨p.swap, swap_mem_diagonal hp, p.swap_swap.symm⟩)

@[simp] lemma one_mul : (1 : mv_power_series σ α) * φ = φ :=
ext $ λ n,
begin
  have H : ((0 : σ →₀ ℕ), n) ∈ (diagonal n) := by simp [mem_diagonal],
  rw [coeff_mul, ← finset.insert_erase H, finset.sum_insert (finset.not_mem_erase _ _),
    coeff_one_zero, one_mul, finset.sum_eq_zero, _root_.add_zero],
  rintros ⟨i,j⟩ hij,
  rw [finset.mem_erase, mem_diagonal] at hij,
  rw [coeff_one, if_neg, _root_.zero_mul],
  intro H, apply hij.1, simp * at *
end

@[simp] lemma mul_one : φ * 1 = φ :=
by rw [mul_comm, one_mul]

lemma mul_add (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, mul_add, finset.sum_add_distrib]

lemma add_mul (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, add_mul, finset.sum_add_distrib]

lemma mul_assoc (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ * φ₂) * φ₃ = φ₁ * (φ₂ * φ₃) :=
ext $ λ n,
begin
  simp only [coeff_mul],
  have := @finset.sum_sigma ((σ →₀ ℕ) × (σ →₀ ℕ)) α _ _ (diagonal n)
    (λ p, diagonal (p.1)) (λ x, coeff x.2.1 φ₁ * coeff x.2.2 φ₂ * coeff x.1.2 φ₃),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl,
    intros p hp, exact finset.sum_mul },
  have := @finset.sum_sigma ((σ →₀ ℕ) × (σ →₀ ℕ)) α _ _ (diagonal n)
    (λ p, diagonal (p.2)) (λ x, coeff x.1.1 φ₁ * (coeff x.2.1 φ₂ * coeff x.2.2 φ₃)),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl, intros p hp, rw finset.mul_sum },
  apply finset.sum_bij,
  swap 5,
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, exact ⟨(k, l+j), (l, j)⟩ },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, simp only [finset.mem_sigma, mem_diagonal] at H ⊢, finish },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, rw mul_assoc },
  { rintros ⟨⟨a,b⟩, ⟨c,d⟩⟩ ⟨⟨i,j⟩, ⟨k,l⟩⟩ H₁ H₂,
    simp only [finset.mem_sigma, mem_diagonal,
      and_imp, prod.mk.inj_iff, add_comm, heq_iff_eq] at H₁ H₂ ⊢,
    finish },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, refine ⟨⟨(i+k, l), (i, k)⟩, _, _⟩;
    { simp only [finset.mem_sigma, mem_diagonal] at H ⊢, finish } }
end

instance : comm_semiring (mv_power_series σ α) :=
{ mul_one := mul_one,
  one_mul := one_mul,
  add_assoc := add_assoc,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  mul_assoc := mul_assoc,
  mul_zero := mul_zero,
  zero_mul := zero_mul,
  mul_comm := mul_comm,
  left_distrib := mul_add,
  right_distrib := add_mul,
  .. mv_power_series.has_zero σ α,
  .. mv_power_series.has_one σ α,
  .. mv_power_series.has_add σ α,
  .. mv_power_series.has_mul σ α }

instance C.is_semiring_hom : is_semiring_hom (C : α → mv_power_series σ α) :=
{ map_zero := C_zero _ _,
  map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_monoid_hom : is_add_monoid_hom (coeff n : mv_power_series σ α → α) :=
{ map_zero := coeff_zero _ _ _,
  map_add := coeff_add n }

instance : semimodule α (mv_power_series σ α) :=
{ smul := λ a φ, C a * φ,
  one_smul := λ φ, one_mul _,
  mul_smul := λ a b φ, by simp only [C_mul, mul_assoc],
  smul_add := λ a φ ψ, mul_add _ _ _,
  smul_zero := λ a, mul_zero _,
  add_smul := λ a b φ, by simp only [C_add, add_mul],
  zero_smul := λ φ, by simp only [zero_mul, C_zero] }

end ring

-- TODO(jmc): once adic topology lands, show that this is complete

end mv_power_series

namespace mv_power_series
variables {σ : Type*} {α : Type*} [decidable_eq σ] [comm_ring α]

protected def neg (φ : mv_power_series σ α) : mv_power_series σ α := λ n, - coeff n φ

instance : has_neg (mv_power_series σ α) := ⟨mv_power_series.neg⟩

@[simp] lemma coeff_neg (φ : mv_power_series σ α) (n) : coeff n (- φ) = - coeff n φ := rfl

lemma add_left_neg (φ : mv_power_series σ α) : (-φ) + φ = 0 :=
ext $ λ n, by rw [coeff_add, coeff_zero, coeff_neg, add_left_neg]

instance : comm_ring (mv_power_series σ α) :=
{ add_left_neg := add_left_neg,
  .. mv_power_series.has_neg, .. mv_power_series.comm_semiring }

instance C.is_ring_hom : is_ring_hom (C : α → mv_power_series σ α) :=
{ map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_group_hom (n : σ →₀ ℕ) :
  is_add_group_hom (coeff n : mv_power_series σ α → α) :=
{ map_add := coeff_add n }

instance : module α (mv_power_series σ α) :=
{ ..mv_power_series.semimodule }

local attribute [instance, priority 0] classical.dec

noncomputable def inv_of_unit (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) : mv_power_series σ α
| n := if n = 0 then ↑u⁻¹ else
- ↑u⁻¹ * finset.sum (n.diagonal) (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
   if h : x.1 < n then inv_of_unit x.1 * coeff x.2 φ else 0)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, finsupp.lt_wf σ⟩],
  dec_tac := tactic.assumption }

end mv_power_series

#exit
import algebra.associated data.finsupp

variables {α : Type*} {σ : Type*} [ring α]

@[reducible] def mv_power_series (σ : Type*) (α : Type*) := (σ →₀ ℕ) → α

instance : has_zero $ mv_power_series σ α := ⟨λ _, 0⟩

def coeff  (x : (σ →₀ ℕ))  (a : (σ →₀ ℕ) → α):= a x

local attribute [instance] classical.dec

def inv_of_unit (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) : mv_power_series σ α
| n := if n = 0 then ↑u⁻¹ else
  - ↑u⁻¹ * finset.sum (n.diagonal) (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if h : x.1 < n then inv_of_unit x.1 * coeff x.2 φ else 0)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, finsupp.lt_wf σ⟩] }

#exit
import data.finsupp
variables {σ : Type}

instance : preorder (σ →₀ ℕ) :=
{ le := λ f g, ∀ s, f s ≤ g s,
  le_refl := λ f s, le_refl _,
  le_trans := λ f g h Hfg Hgh s, le_trans (Hfg s) (Hgh s) }
#print finset.sum_le
lemma sum_lt_sum_of_lt (f g : σ →₀ ℕ) : f < g → f.sum (λ _, id) < g.sum (λ _, id) :=
begin
  assume hfg,
  cases  classical.not_forall.1 hfg.2 with i hi,
  rw finsupp.sum,

end

#exit
import set_theory.schroeder_bernstein

universe u

structure B := (C : Type u)

lemma eq.mpr_injective {α β : Sort u} (h : α = β) :
  function.injective (eq.mpr h) := λ _ _, by cases h; exact id

instance : inhabited B := ⟨⟨pempty⟩⟩

open function

example {α : Type u} (f : B.{u} ↪ α) : false :=
let g := B.C ∘ inv_fun f in
have hg : surjective g, from
  surjective_comp (λ x, ⟨B.mk x, rfl⟩) (inv_fun_surjective f.2),
let X : Type u := sigma g in
let a : α := classical.some (hg (X → Prop)) in
have ha : g a = (X → Prop), from classical.some_spec (hg (set X)),
cantor_injective (show set X → X, from λ s, ⟨a, by rw ha; exact s⟩)
  (λ x y h, by simp at *; exact eq.mpr_injective _ h)

#exit
import ring_theory.ideal_operations
universe u
variables {R : Type u} [comm_ring R]

def ar : lattice.complete_lattice (ideal R) := by apply_instance
#print lattice.lt
instance : ordered_comm_monoid (ideal R) :=
{ le := (≤),
  add_le_add_left := λ a b hab c, lattice.sup_le_sup (le_refl _) hab,
  lt_of_add_lt_add_left := λ a b c h, begin
    refine not_lt

  end,
  --add_left_cancel := _,
  ..ideal.comm_semiring,
  ..submodule.lattice.complete_lattice
  --show lattice.complete_lattice (ideal R), by apply_instance
  }

#exit
import data.multiset data.finsupp
import category_theory.natural_isomorphism category_theory.types category_theory.opposites category_theory.concrete_category

universe u

open category_theory

namespace category_theory.instances

@[reducible] def DecEq := bundled decidable_eq

instance (x : DecEq) : decidable_eq x := x.str

instance DecEq_category : category DecEq :=
{ hom := λ x y, x → y,
  id := λ x, id,
  comp := λ x y z f g, g ∘ f }

end category_theory.instances

open category_theory.instances

@[reducible] def Multiset : DecEq.{u} ⥤ Type u :=
{ obj := λ α, multiset α,
  map := λ α β, multiset.map,
  map_id' := λ α, funext multiset.map_id,
  map_comp' := λ α β γ f g, funext $ λ s, (multiset.map_map g f s).symm }

@[reducible] def Finsupp_nat : DecEq.{u} ⥤ Type u :=
{ obj := λ α, α →₀ ℕ,
  map := λ α β, finsupp.map_domain,
  map_id' := λ α, funext $ λ s, finsupp.map_domain_id,
  map_comp' := λ α β γ f g, funext $ λ s, finsupp.map_domain_comp }

theorem multiset.map_repeat {α : Type u} {β : Type*} (f : α → β) (x : α) (n : ℕ) :
  multiset.map f (multiset.repeat x n) = multiset.repeat (f x) n :=
nat.rec_on n rfl $ λ n ih, by rw [multiset.repeat_succ, multiset.map_cons, ih, multiset.repeat_succ]

theorem multiset.repeat_add {α : Type u} (x : α) (m n : ℕ) :
  multiset.repeat x (m + n) = multiset.repeat x m + multiset.repeat x n :=
nat.rec_on n (by rw [multiset.repeat_zero, add_zero, add_zero]) $ λ n ih,
by rw [multiset.repeat_succ, nat.add_succ, multiset.repeat_succ, multiset.add_cons, ih]

-- ⟨s.to_finset, λ x, s.count x, λ x, multiset.mem_to_finset.trans $ multiset.count_pos.symm.trans $ nat.pos_iff_ne_zero⟩
-- faster but less idiomatic
def Multiset_Finsupp_nat : Multiset.{u} ≅ Finsupp_nat.{u} :=
{ hom :=
  { app := λ α s, { to_fun := λ a, s.count a,
      support := s.to_finset,
      mem_support_to_fun := by simp [multiset.count_eq_zero] },
    naturality' := λ X Y f, begin
      dsimp, simp [function.funext_iff, finsupp.ext_iff],
      unfold_coes,
      dsimp [finsupp.map_domain],

    end },
  inv :=
  { app := λ α s, s.sum multiset.repeat,
    naturality' := λ α β f, funext $ λ s,
      show (s.map_domain f).sum multiset.repeat = (s.sum multiset.repeat).map f,
      from finsupp.induction s rfl $ λ x n s hsx hn ih, begin
        rw [finsupp.map_domain_add, finsupp.sum_add_index, finsupp.map_domain_single, finsupp.sum_single_index,
            finsupp.sum_add_index, finsupp.sum_single_index, multiset.map_add, multiset.map_repeat, ih],
        { refl }, { intros, refl }, { intros, rw multiset.repeat_add },
        { refl }, { intros, refl }, { intros, rw multiset.repeat_add }
      end },
  hom_inv_id' := nat_trans.ext $ λ α, funext $ λ s,
    show (s.map $ λ x, finsupp.single x 1).sum.sum multiset.repeat = s,
    from multiset.induction_on s rfl $ λ a s ih, begin
      rw [multiset.map_cons, multiset.sum_cons, finsupp.sum_add_index, finsupp.sum_single_index, multiset.repeat_one, ih, multiset.cons_add, zero_add],
      { refl }, { intros, refl }, { intros, rw multiset.repeat_add }
    end,
  inv_hom_id' := nat_trans.ext $ λ α, funext $ λ s,
    show ((s.sum multiset.repeat).map $ λ x, finsupp.single x 1).sum = s,
    from finsupp.induction s rfl $ λ y n s hsy hn ih, begin
      rw [finsupp.sum_add_index, finsupp.sum_single_index, multiset.map_add, multiset.sum_add, ih, multiset.map_repeat],
      { congr' 1, clear hn, induction n with n ih,
        { rw [finsupp.single_zero, multiset.repeat_zero, multiset.sum_zero] },
        { rw [multiset.repeat_succ, multiset.sum_cons, ih, ← nat.one_add, finsupp.single_add] } },
      { refl }, { intros, refl }, { intros, rw multiset.repeat_add }
    end }

#exit
import data.num.basic
set_option profiler true
namespace nat

def fib : ℕ → ℕ
|     0 := 1
|     1 := 1
| (n+2) := fib n + fib (n+1)

def fib2 : ℕ → ℕ × ℕ
|     0 := (1, 0)
| (n+1) := let x := fib2 n in (x.1 + x.2, x.1)

def fib3 : ℕ → ℕ × ℕ
|     0 := (1, 0)
| (n+1) := ((fib3 n).1 + (fib3 n).2, (fib3 n).1)

def fib4 : ℕ → ℕ × ℕ
|     0 := (1, 0)
| (n+1) :=
  match fib4 n with
  | (x, y) := (x + y, x)
  end

#eval fib3 10
#eval fib4 100000
#eval fib2 100000
end nat

namespace num

def fib : ℕ → num
|     0 := 1
|     1 := 1
| (n+2) := fib n + fib (n+1)

def fib2 : ℕ → num × num
|     0 := (1, 0)
| (n+1) := let x := fib2 n in
  (x.1 + x.2, x.1)

def fib3 : ℕ → num × num
|     0 := (1, 0)
| (n+1) := ((fib3 n).1 + (fib3 n).2, (fib3 n).1)

def fib4 : ℕ → num × num
|     0 := (1, 0)
| (n+1) :=
  match fib4 n with
  | (x, y) := (x + y, x)
  end
--#reduce fib2 30
#reduce fib2 20
#reduce fib3 20
#reduce fib4 22

end num

set_option profiler true

-- #reduce fib 40

#eval fib3 100000

#exit
import data.nat.basic
open nat
theorem even_ne_odd {n m} : 2 * n ≠ 2 * m + 1 :=
mt (congr_arg (%2)) (by rw [add_comm, add_mul_mod_self_left, mul_mod_right]; exact dec_trivial)
#print even_ne_odd
#exit
import logic.function tactic
open monad

section

inductive p : Prop
| mk : p → p

example : ¬ p := λ h, by induction h; assumption

parameters {m : Type → Type} [monad m] [is_lawful_monad m]

inductive mem : Π {α : Type}, α → m α → Prop
| pure : ∀ {α : Type} (a : α), mem a (pure a)
| join : ∀ {α : Type} (a : α) (b : m α) (c : m (m α)), mem a b → mem b c →
  mem a (monad.join c)

parameters (mem2 : Π {α : Type}, α → m α → Prop)
  (mem2_pure : ∀ {α : Type} (a b : α), mem2 a (pure b) ↔ a = b)
  (mem2_bind : Π {α : Type} (a : α) (c : m (m α)),
    mem2 a (join c) ↔ ∃ b : m α, mem2 a b ∧ mem2 b c)

example (mem2 : Π {α : Type}, α → m α → Prop)
  (mem2_pure : ∀ {α : Type} {a b : α}, mem2 a (pure b) ↔ a = b)
  (mem2_join : Π {α : Type} (a : α) (c : m (m α)),
    mem2 a (join c) ↔ ∃ b : m α, mem2 a b ∧ mem2 b c)
  {α : Type} {a : α} (b : m α) (h : mem a b) : mem2 a b :=
by induction h; simp *; tauto

end

section

parameters {m : Type → Type} [monad m] [is_lawful_monad m]

inductive mem : Π {α : Type}, α → m α → Prop
| pure : ∀ {α : Type} (a : α), mem a (pure a)
| join : ∀ {α : Type} (a : α) (b : m α) (c : m (m α)), mem a b → mem b c →
  mem a (monad.join c)

parameters (mem2 : Π {α : Type}, α → m α → Prop)
  (mem2_pure : ∀ {α : Type} (a b : α), mem2 a (pure b) ↔ a = b)
  (mem2_bind : Π {α : Type} (a : α) (c : m (m α)),
    mem2 a (join c) ↔ ∃ b : m α, mem2 a b ∧ mem2 b c)

example (mem2 : Π {α : Type}, α → m α → Prop)
  (mem2_pure : ∀ {α : Type} {a b : α}, mem2 a (pure b) ↔ a = b)
  (mem2_join : Π {α : Type} (a : α) (c : m (m α)),
    mem2 a (join c) ↔ ∃ b : m α, mem2 a b ∧ mem2 b c)
  {α : Type} {a : α} (b : m α) (h : mem a b) : mem2 a b :=
by induction h; simp *; tauto

end

#exit
import data.matrix data.equiv.algebra

def one_by_one_equiv (one R : Type*) [unique one] [ring R] : matrix one one R ≃ R :=
{ to_fun := λ M, M (default _) (default _),
  inv_fun := λ x _ _, x,
  left_inv := λ _, matrix.ext
    (λ i j, by rw [unique.eq_default i, unique.eq_default j]),
  right_inv := λ _, rfl }

lemma one_by_one_equiv.is_ring_hom (one R : Type*) [unique one] [ring R] :
  is_ring_hom (one_by_one_equiv one R) :=
{ map_one := rfl,
  map_add := λ _ _, rfl,
  map_mul := λ _ _, by dsimp [one_by_one_equiv, matrix.mul]; simp }

def one_by_one_ring_equiv (one R : Type*) [unique one] [ring R] : matrix one one R ≃r R :=
{ hom := one_by_one_equiv.is_ring_hom one R,
  ..one_by_one_equiv one R }

import data.finset

#check @finset.sup

#exit
import measure_theory.giry_monad
universe u

variables {α : Type u} {β : Type u}
open nat

example {n : ℕ} : n ≤ n * n :=
begin
induction n_eq : n with m IH,
all_goals {
  have : 0 ≤ n, from n.zero_le
},
{ simp },
{ sorry }
end

lemma rubbish (n m : ℕ) (h : n = m) (hm : m ≠ 1) : n = 0 ∨ n > m :=
begin
  induction n,
  { left, refl },
  { -- case nat.succ
    -- m : ℕ,
    -- hm : m ≠ 1,
    -- n_n : ℕ,
    -- n_ih : n_n = m → n_n = 0 ∨ n_n > m,
    -- h : succ n_n = m
    -- ⊢ succ n_n = 0 ∨ succ n_n > m
    have : n_n = 0 ∨ n_n > m, from sorry,
    cases this,
    subst this, exfalso,
    exact hm h.symm,
    exact or.inr (lt_succ_of_lt this) }
end

example : false := absurd (rubbish 2 2) dec_trivial

open measure_theory measure_theory.measure

lemma inl_measurable_bind_ret [measurable_space α] [measurable_space β] (ν : measure β) :
  measurable (λ (x : α), bind ν (λ y, dirac (x, y))) :=
begin





end

#print measure.join

lemma inl_measurable_bind_ret' [measurable_space α] [measurable_space β] (w : measure β) :
  measurable (λ (x : α), bind w (λ y, dirac (x, y))) :=
have ∀ x : α, measurable (@prod.mk α β x),
  from λ x, measurable_prod_mk measurable_const measurable_id,
begin
  dsimp [measure.bind],
  conv in (map _ _) { rw [← measure.map_map measurable_dirac (this x)] },
  refine measurable_join.comp _,
  refine measurable.comp _ _,
  { refine measurable_map _ measurable_dirac },
  { sorry }




end

#exit


import data.equiv.encodable data.fintype

def f : bool → bool → bool
| tt tt := ff
| _ _   := tt
#print as_true
local notation `dec_trivial'` := of_as_true trivial

example : (∀ x y, f x y = f y x) ∧
  ¬(∀ x y z, f x (f y z) = f (f x y) z) := dec_trivial'

#eval ((finset.univ : finset (bool → bool → bool)).filter
  (λ f : bool → bool → bool, (∀ x y, f x y = f y x) ∧
  ¬(∀ x y z, f x (f y z) = f (f x y) z))).1.unquot.nth_le 0
  sorry ff ff


#exit
import data.finsupp order.complete_lattice algebra.ordered_group

namespace finsupp
open lattice
variables {σ : Type*} {α : Type*} [decidable_eq σ]

instance [preorder α] [has_zero α] : preorder (σ →₀ α) :=
{ le := λ f g, ∀ s, f s ≤ g s,
  le_refl := λ f s, le_refl _,
  le_trans := λ f g h Hfg Hgh s, le_trans (Hfg s) (Hgh s) }

instance [partial_order α] [has_zero α] : partial_order (σ →₀ α) :=
{ le_antisymm := λ f g hfg hgf, finsupp.ext $ λ s, le_antisymm (hfg s) (hgf s),
  .. finsupp.preorder }

instance [canonically_ordered_monoid α] : order_bot (σ →₀ α) :=
{ bot := 0,
  bot_le := λ f s, zero_le _,
  .. finsupp.partial_order }

def finsupp.of_pfun {α β : Type*} [has_zero β] [decidable_eq α] [decidable_eq β]
  (s : finset α) (f : Πa ∈ s, β) : α →₀ β :=
{ to_fun := λ a, if h : a ∈ s then f a h else 0,
  support := s.filter (λ a, ∃ h : a ∈ s, f a h ≠ 0),
    mem_support_to_fun := begin intros,
      simp only [finset.mem_def.symm, finset.mem_filter],
      split_ifs;
      split; {tauto <|> finish}
    end,  }

def downset [preorder α] (a : α) := {x | x ≤ a}
#print finsupp
lemma nat_downset (f : σ →₀ ℕ) : finset (σ →₀ ℕ) :=
(f.support.pi (λ s, finset.range (f s))).map
  ⟨_, _⟩

lemma nat_downset_eq_downset (f : σ →₀ ℕ) :
  (↑(nat_downset f) : set (σ →₀ ℕ)) = downset f := sorry

end finsupp
#exit
def r : ℕ → ℕ → Prop := classical.some (show ∃ r : ℕ → ℕ → Prop,
  equivalence r ∧ ∀ a c b d,
  r a b → r c d → r (a + c) (b + d), from ⟨(=), ⟨eq.refl, λ _ _, eq.symm, λ _ _ _, eq.trans⟩,
    by intros; simp *⟩)

instance X_setoid : setoid ℕ := ⟨r, (classical.some_spec r._proof_1).1⟩

def X : Type := quotient ⟨r, (classical.some_spec r._proof_1).1⟩


--computable
def add : X → X → X := λ a b, quotient.lift_on₂ a b
  (λ a b, ⟦a + b⟧)
  (λ a b c d hab hcd,
    quotient.sound $ (classical.some_spec r._proof_1).2 _ _ _ _ hab hcd)

#exit
import logic.basic tactic data.finset data.complex.basic data.polynomial
#print option.bind

lemma Z : has_sizeof (ℕ → ℕ) := by apply_instance
#eval sizeof ([] : list Type)
#eval sizeof (0 : polynomial (polynomial ℚ))
set_option pp.all true
#print Z

#print (infer_instance : )

#eval list.sizeof [@id ℕ]
#reduce λ α : Type, has_sizeof.sizeof α

inductive list2 : Type
| nil : list2
| cons : ℕ → ℕ → list2 → list2

#eval sizeof list2.nil

example {α: ℕ → Type u} (x y: ℕ) (a: α (x+y)) (b: α (y+x)) (h: a == b): true := begin
  -- i want (h: a = b)
  -- rw [nat.add_comm] at a, -- h still depends on old (a: α (x+y)) :<
  -- have h: a = b := eq_of_heq h, -- fail

  rw [nat.add_comm] at a,
  intros a b h,
  have h: a = b := eq_of_heq h, -- good

  trivial,
end

example (X Y : Type) (f : X → Y) (hf : function.bijective f) : ∃ g : Y → X, true :=
⟨λ y, hf _, trivial⟩

#exit

import data.polynomial



#print finset.prod_sum

set_option pp.proofs true
#print eq.drec
open polynomial
#eval ((finset.range 9).sum (λ n, (X : polynomial ℕ) ^ n)) ^ 5

#eval let k := 2 in ((k + 1) * (k + 2) * (k + 3) * (k + 4)) / nat.fact 4

#eval nat.choose 3 4

#exit
import algebra.char_p
#print classical.em
#print rel.comp
set_option pp.implicit true
set_option pp.notation false


lemma X : (⟨bool, tt⟩ : Σ α : Type, α) ≠ ⟨bool, ff⟩ :=
λ h, by cases h


#print X
#exit

import topology.opens

open topological_space continuous

def opens.what_is_this_called {X : Type*} [topological_space X]
  {U V : opens X} : opens V :=
U.comap

def well_ordering_rel {α : Type*} : α → α → Prop :=
classical.some well_ordering_thm

instance {α : Type*} : is_well_order α well_ordering_rel :=
classical.some_spec well_ordering_thm

local attribute [instance] classical.dec

noncomputable example {M : Type u → Type u} [monad M]
  {α β : Type u} (f : β → M α) : M (β → α) :=
let g : β → M (β → α) := λ i : β, (do x ← f i, return (λ _, x)) in
if h : nonempty β then g (classical.choice h) else return (λ i : β, false.elim (h ⟨i⟩))

example {M : Type u → Type u} [monad M] {α β : Type u} : (β → M α) → M (β → α) :=
let r := @well_ordering_rel β in
have h : Π a : β, ({x // r x a} → M α) → M ({x // r x a} → α),
  from well_founded.fix (show well_founded r, from sorry)
    (λ a ih f, do g ← ih a _ _, _),
begin



end

#print monad


#print is_lawful_monad
#print vector.traverse
import data.nat.basic tactic.ring

lemma silly (n d : ℕ) :  2 * (2 ^ n * d + 2 ^ n * 1) - 2 * 1 + 1 =
  2 ^ n * 2 * 1 + 2 ^ n * 2 * d - 1 :=
begin
  rw [mul_one 2, bit0, ← nat.sub_sub, nat.sub_add_cancel];
  ring,


end


#exit

noncomputable theory

open set function continuous

section homotopy

variables {X : Type*} [topological_space X]
variables {Y : Type*} [topological_space Y]
variables {Z : Type*} [topological_space Z]

lemma Union_inter_subset {α ι : Type*} {s t : ι → set α} :
  (⋃ i, (s i ∩ t i)) ⊆ (⋃ i, s i) ∩ (⋃ i, t i) :=
by finish [set.subset_def]

lemma Inter_union_subset {α ι : Type*} {s t : ι → set α} :
  (⋂ i, s i) ∪ (⋂ i, t i) ⊆ (⋂ i, (s i ∪ t i)) :=
by finish [set.subset_def]

local attribute [instance]classical.dec
/- pasting or gluing lemma: if a continuous function is continuous on finitely many
  closed subsets, it is continuous on the Union -/
theorem continuous_on_Union_of_closed {ι : Type*} [fintype ι]
  {s : ι → set X} (hs : ∀ i, is_closed (s i)) {f : X → Y}
  (h : ∀ i, continuous_on f (s i)) : continuous_on f (⋃ i, s i) :=
begin
  simp only [continuous_on_iff, mem_Union, exists_imp_distrib] at *,
  assume x i hi t ht hfxt,
  have h' : ∃ v : Π i, x ∈ s i → set X, ∀ i hi,
    is_open (v i hi) ∧ x ∈ v i hi ∧ v i hi ∩ s i ⊆ f ⁻¹' t,
  { simpa only [classical.skolem] using λ i hi, h i x hi t ht hfxt },
  cases h' with v hv,
  use ⋂ (i : ι), (⋂ (hi : x ∈ s i), v i hi) ∩ (⋂ (hi : x ∉ s i), -s i),
  refine ⟨is_open_Inter (λ j, is_open_inter
      (is_open_Inter_prop (λ _, (hv _ _).1))
      (is_open_Inter_prop (λ _, hs _))),
    mem_Inter.2 (λ j, mem_inter (mem_Inter.2 (λ _, (hv _ _).2.1)) (mem_Inter.2 id)),
    _⟩,
  assume y hy,
  simp only [mem_Inter, mem_inter_eq] at hy,
  cases mem_Union.1 hy.2 with j hyj,
  have hxj : x ∈ s j, from classical.by_contradiction (λ hxj, (hy.1 j).2 hxj hyj),
  exact (hv j hxj).2.2 ⟨(hy.1 j).1 _, hyj⟩
end

theorem continuous_on_Union_of_open {ι : Sort*}
  {s : ι → set X} (hs : ∀ i, is_open (s i)) {f : X → Y}
  (h : ∀ i, continuous_on f (s i)) : continuous_on f (⋃ i, s i) :=
begin
  simp only [continuous_on_iff, mem_Union, exists_imp_distrib] at *,
  assume x i hi t ht hfxt,
  have h' : ∃ v : Π i, x ∈ s i → set X, ∀ i hi,
    is_open (v i hi) ∧ x ∈ v i hi ∧ v i hi ∩ s i ⊆ f ⁻¹' t,
  { simpa only [classical.skolem] using λ i hi, h i x hi t ht hfxt },
  cases h' with v hv,
  use v i hi ∩ s i,
  use is_open_inter (hv _ _).1 (hs i),
  use mem_inter (hv _ _).2.1 hi,
  use subset.trans (inter_subset_left _ _) (hv i hi).2.2
end

lemma Inter_cond {α : Type*} {s t : set α} : (⋂ (i : bool), cond i t s) = s ∩ t :=
@Union_cond

lemma continuous_on_union_of_closed {s t : set X} (hsc : is_closed s)
  (htc : is_closed t) {f : X → Y} (hsf : continuous_on f s)
  (htf : continuous_on f t) : continuous_on f (s ∪ t) :=
by rw [← Union_cond]; exact continuous_on_Union_of_closed
  (λ i, bool.cases_on i hsc htc) (λ i, bool.cases_on i hsf htf)

lemma continuous_on_union_of_open {s t : set X} (hsc : is_open s)
  (htc : is_open t) {f : X → Y} (hsf : continuous_on f s)
  (htf : continuous_on f t) : continuous_on f (s ∪ t) :=
by rw [← Union_cond]; exact continuous_on_Union_of_open
  (λ i, bool.cases_on i hsc htc) (λ i, bool.cases_on i hsf htf)

#exit
import data.rat.denumerable
open encodable function lattice

namespace nat.subtype

variables {s : set ℕ} [decidable_pred s] [infinite s]

lemma exists_succ (x : s) : ∃ n, x.1 + n + 1 ∈ s :=
classical.by_contradiction $ λ h,
have ∀ (a : ℕ) (ha : a ∈ s), a < x.val.succ,
  from λ a ha, lt_of_not_ge (λ hax, h ⟨a - (x.1 + 1),
    by rwa [add_right_comm, nat.add_sub_cancel' hax]⟩),
infinite.not_fintype
  ⟨(((multiset.range x.1.succ).filter (∈ s)).pmap
      (λ (y : ℕ) (hy : y ∈ s), subtype.mk y hy)
      (by simp [-multiset.range_succ])).to_finset,
    by simpa [subtype.ext, multiset.mem_filter, -multiset.range_succ]⟩

def succ (x : s) : s :=
have h : ∃ m, x.1 + m + 1 ∈ s, from exists_succ x,
⟨x.1 + nat.find h + 1, nat.find_spec h⟩

lemma succ_le_of_lt {x y : s} (h : y < x) : succ y ≤ x :=
have hx : ∃ m, y.1 + m + 1 ∈ s, from exists_succ _,
let ⟨k, hk⟩ := nat.exists_eq_add_of_lt h in
have nat.find hx ≤ k, from nat.find_min' _ (hk ▸ x.2),
show y.1 + nat.find hx + 1 ≤ x.1,
by rw hk; exact add_le_add_right (add_le_add_left this _) _

lemma le_succ_of_forall_lt_le {x y : s} (h : ∀ z < x, z ≤ y) : x ≤ succ y :=
have hx : ∃ m, y.1 + m + 1 ∈ s, from exists_succ _,
show x.1 ≤ y.1 + nat.find hx + 1,
from le_of_not_gt $ λ hxy,
have y.1 + nat.find hx + 1 ≤ y.1 := h ⟨_, nat.find_spec hx⟩ hxy,
not_lt_of_le this $
  calc y.1 ≤ y.1 + nat.find hx : le_add_of_nonneg_right (nat.zero_le _)
  ... < y.1 + nat.find hx + 1 : nat.lt_succ_self _

lemma lt_succ_self (x : s) :  x < succ x :=
calc x.1 ≤ x.1 + _ : le_add_right (le_refl _)
... < succ x : nat.lt_succ_self (x.1 + _)

def of_nat (s : set ℕ) [decidable_pred s] [infinite s] : ℕ → s
| 0     := ⊥
| (n+1) := succ (of_nat n)

lemma of_nat_strict_mono : strict_mono (of_nat s) :=
nat.strict_mono_of_lt_succ (λ a, by rw of_nat; exact lt_succ_self _)

open list

lemma of_nat_surjective_aux : ∀ {x : ℕ} (hx : x ∈ s), ∃ n, of_nat s n = ⟨x, hx⟩
| x := λ hx, let t : list s := ((list.range x).filter (λ y, y ∈ s)).pmap
  (λ (y : ℕ) (hy : y ∈ s), ⟨y, hy⟩) (by simp) in
have hmt : ∀ {y : s}, y ∈ t ↔ y < ⟨x, hx⟩,
  by simp [list.mem_filter, subtype.ext, t]; intros; refl,
if ht : t = [] then ⟨0, le_antisymm (@bot_le s _ _)
  (le_of_not_gt (λ h, list.not_mem_nil ⊥ $
    by rw [← ht, hmt]; exact h))⟩
else by letI : inhabited s := ⟨⊥⟩;
  exact have wf : (maximum t).1 < x, by simpa [hmt] using list.mem_maximum ht,
  let ⟨a, ha⟩ := of_nat_surjective_aux (list.maximum t).2 in
  ⟨a + 1, le_antisymm
    (by rw of_nat; exact succ_le_of_lt (by rw ha; exact wf)) $
    by rw of_nat; exact le_succ_of_forall_lt_le
      (λ z hz, by rw ha; exact list.le_maximum_of_mem (hmt.2 hz))⟩

lemma of_nat_surjective : surjective (of_nat s) :=
λ ⟨x, hx⟩, of_nat_surjective_aux hx

def denumerable (s : set ℕ) [decidable_pred s] [infinite s] : denumerable s :=
have li : left_inverse (of_nat s) (λ x : s, nat.find (of_nat_surjective x)),
  from λ x, nat.find_spec (of_nat_surjective x),
denumerable.of_equiv ℕ
{ to_fun := λ x, nat.find (of_nat_surjective x),
  inv_fun := of_nat s,
  left_inv := li,
  right_inv := right_inverse_of_injective_of_left_inverse
    (strict_mono.injective of_nat_strict_mono) li }

end nat.subtype

variables {α : Type*} [encodable α] [decidable_eq α]

def decidable_range_encode : decidable_pred (set.range (@encode α _)) :=
λ x, decidable_of_iff (option.is_some (decode2 α x))
  ⟨λ h, ⟨option.get h, by rw [← decode2_is_partial_inv (option.get h), option.some_get]⟩,
  λ ⟨n, hn⟩, by rw [← hn, encodek2]; exact rfl⟩

variable [infinite α]

def demumerable_of_encodable_of_infinite : denumerable α :=
by letI := @decidable_range_encode α _ _;
  letI : infinite (set.range (@encode α _)) :=
    infinite.of_injective _ (equiv.set.range _ encode_injective).injective;
  letI := nat.subtype.denumerable (set.range (@encode α _)); exact
denumerable.of_equiv (set.range (@encode α _))
{ to_fun := _ }

#exit
import topology.instances.real

lemma bool_ne_nat : bool ≠ nat :=
begin


end

#print set.image_preimage_eq
instance z : topological_space Prop := by apply_instance
#print sierpinski_space
#print topological_space.generate_from
#print continuous_generated_from

example {α : Type*} [topological_space α] : continuous (eq : α → α → Prop) :=
continuous_pi (λ x, _)

example {α : Type*} [topological_space α] {s : α → Prop} :
  continuous s ↔ is_open s :=
⟨λ h, by convert h {true} (by simp); simp [eq_true, set.preimage, set_of],
  λ _, continuous_generated_from $ by simpa [set.preimage, eq_true, set_of]⟩

def foo : nat → Prop
| 0 := true
| (n+1) := (foo n) ∧ (foo n)

meta def mk_foo_expr : nat → expr
| 0 := `(trivial)
| (n+1) :=
  expr.app
    (expr.app
      (reflected.to_expr `(@and.intro (foo n) (foo n)))
      (mk_foo_expr n))
    (mk_foo_expr n)

open tactic

meta def show_foo : tactic unit :=
do `(foo %%nx) ← target,
   n ← eval_expr nat nx,
   exact (mk_foo_expr n)

set_option profiler true

lemma foo_200 : foo 500 :=
by show_foo

#print foo_200
#exit
import tactic category_theory.limits.types

def colimit_cocone {J Y : Type} {X : J → Type} (t : Π j : J, X j → Y)
  (h : ∀ {α : Type} (f g : Y → α), (∀ j x, f (t j x) = g (t j x)) → f = g) :
  ∀ y : Y, ∃ j x, t j x = y :=
@eq.rec _ _ (λ P : Y → Prop, ∀ y, P y)
    (λ _, true.intro) _
    (@h Prop (λ _, true)
    (λ y, ∃ j x, t j x = y)
    (λ j x, propext ⟨λ _, ⟨j, x, eq.refl _⟩,
      λ _, true.intro⟩))
#print category_theory.functor.id
open category_theory

def fin_functor : functor ℕ Type :=
{ obj := fin,
  map := λ a b ⟨⟨h⟩⟩ i, ⟨i.1, lt_of_lt_of_le i.2 h⟩ }
#print functor.obj
def type_of {α : Sort*} (x : α) : Sort* := α
#reduce type_of (limits.types.colimit.{0} fin_functor).ι.app

example : sorry :=
begin
  have := @colimit_cocone ℕ _ _
    ((limits.types.colimit.{0} fin_functor).ι.app) begin

     end,

end

#print colimit_cocone
#reduce colimit_cocone
#reduce propext
#exit
import data.vector2

inductive expression : Type
| a {dim : ℕ} (v : fin dim → expression) /- omitted constraints on dim -/ : expression
| b : expression
open expression

#print expression.sizeof
#print vector.of_fn
def f (e : expression) : ℕ :=
expression.rec_on e
  (λ n idx f, 1 + (vector.of_fn f).1.sum)
  1

def f : expression -> ℕ
| (a idx) := 1 + ((vector.of_fn (λ x, idx x)).map f).1.sum

--using_well_founded {rel_tac := λ_ _, `[exact ⟨_, measure_wf (λ e, expression_size e)⟩] }

#exit

import data.rat.basic algebra.archimedean

lemma lt_of_mul_lt_mul_left' {α : Type*} [ordered_ring α]
  {a b c : α} (hc : c ≥ 0) (h : c * a < c * b) : a < b := sorry

lemma div_le_div {a b : ℤ} : ((a / b : ℤ) : ℚ) ≤ a / b :=
if hb : b = 0 then by simp [hb]
else
have hb0 : 0 < (b : ℚ), from nat.cast_pos.2 _,
le_of_mul_le_mul_left (@le_of_add_le_add_left ℚ _ (a % b : ℤ) _ _
  begin
    rw [← int.cast_mul, ← int.cast_add, int.mod_add_div,
      mul_div_cancel', add_comm],
    exact le_add_of_le_of_nonneg (le_refl _)
      (int.cast_nonneg.2 (int.mod_nonneg _ hb)),
  end)
hb0

lemma div_eq_rat_floor (n : ℤ) (d : ℕ) : n / d = ⌊(n : ℚ) / d⌋ :=
if h : d = 0 then by simp [h]
else
have hd0 : (d : ℚ) ≠ 0, by simpa,
have hd0' : 0 < (d : ℚ), from sorry,
le_antisymm
  (le_floor.2 _)
  (int.le_of_lt_add_one $ floor_lt.2 (lt_of_mul_lt_mul_left'
    (show (0 : ℚ) ≤ d, from nat.cast_nonneg _)
    (begin
        rw [mul_div_cancel' _ hd0, int.cast_add, add_comm, mul_add,
          int.cast_one, mul_one],
        conv {to_lhs, rw ← int.mod_add_div n d},
        simp,
        rw [← int.cast_coe_nat d, int.cast_lt],
        convert int.mod_lt _ (int.coe_nat_ne_zero.2 h),
        simp
      end)))


open nat

inductive le' (a : ℕ) : ℕ → Prop
| refl : le' a
| succ : ∀ b, le' b → le' (succ b)

infix ` ≤' `: 50 := le'

lemma le'_trans {a b c : ℕ} (hab : a ≤' b) (hbc : b ≤' c) : a ≤' c :=
le'.rec_on hbc hab (λ _ _, le'.succ _)

def lt' (a b : ℕ) : Prop :=
succ a ≤' b

infix ` <' `:50 := lt'

lemma le_of_lt' {a b : ℕ} (h : a <' b) : a ≤' b :=
le'.rec_on h (le'.succ _ (le'.refl _)) (λ _ _, le'.succ _)

lemma b (a b c : ℕ) (hab : a <' b) (hbc : b <' c) : a <' c :=
le'_trans hab (le_of_lt' hbc)

#reduce b 3 4 5 (le'.refl _) (le'.refl _)

#exit
import algebra.module
import group_theory.group_action
import linear_algebra.basic -- this import breaks the commented lines at the end of the file

class group_module (G M : Type) [monoid G] [add_comm_group M]
  extends mul_action G M :=
(smul_add  : ∀ (g : G) (m₁ m₂ : M), g • (m₁ + m₂) = g • m₁ + g • m₂)

attribute [simp] group_module.smul_add

namespace fixed_points
open mul_action
variables {G M : Type}
variables [monoid G] [add_comm_group M]
variable [group_module G M]

lemma add_mem (x y : M) (hx : x ∈ fixed_points G M) (hy : y ∈ fixed_points G M) :
  x + y ∈ fixed_points G M :=
begin
  intro g,
  simp only [mem_stabilizer_iff, group_module.smul_add, mem_fixed_points] at *,
  rw [hx, hy],
end

end fixed_points

class representation (G R M : Type) [monoid G] [ring R] [add_comm_group M] [module R M]
  extends group_module G M :=
(smul_comm : ∀ (g : G) (r : R) (m : M), g • (r • m) = r • (g • m))

--namespace representation
--open mul_action linear_map


variables {G R M : Type}
variables [group G] [ring R] [ring M] [module R M] [representation G R M]

set_option trace.class_instances true
--set_option class_

lemma smul_mem_fixed_points (r : R) (m : M) (hm : m ∈ mul_action.fixed_points G M) :
  (r • m : M) = sorry :=
begin
  simp only [mem_fixed_points] at *,
  intro g,
  rw [smul_comm, hm],
end
end representation


import data.equiv.basic order.zorn
open function set zorn

variables {α : Type*} {β : Type*} [nonempty β]

instance m : partial_order (α → β) :=
{ le := λ x y, range x ⊆ range y ∧ ∀ a, y a ∈ range x → y a = x a,
  le_trans := λ x y z hxy hyz, ⟨subset.trans hxy.1 hyz.1,
    λ a ha, begin
      rw [hyz.2 a (hxy.1 ha), hxy.2 a],
      rwa [← hyz.2 a (hxy.1 ha)]
    end⟩,
  le_refl := λ _, ⟨subset.refl _, λ _ _, rfl⟩,
  le_antisymm := λ x y hxy hyx,
    by simp only [subset.antisymm hxy.1 hyx.1] at *;
    exact funext (λ a, (hxy.2 _ ⟨a, rfl⟩).symm) }


example : ∃ f : α → β, ∀ g, f ≤ g → g ≤ f :=
zorn _
  (λ _ _ _, le_trans)

example {α β : Type*} [nonempty β] : {f : α → β // injective f ∨ surjective f} :=
let r :

begin


end


#exit
import data.list.basic

#print has_to
#print galois_insterion
@[derive decidable_eq] inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml
infixr ` →' `:50 := imp -- right associative

prefix `¬' `:51 := fml.not

inductive prf : fml → Type
| axk {p q} : prf (p →' q →' p)
| axs {p q r} : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX {p q} : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

instance (p): has_sizeof (prf p) := by apply_instance

open prf

meta def length {f : fml} (t : prf f) : ℕ :=
prf.rec_on t (λ _ _, 1) (λ _ _ _, 1) (λ _ _, 1) (λ _ _ _ _, (+))

instance (p q : fml) : has_coe_to_fun (prf (p →' q)) :=
{ F := λ x, prf p → prf q,
  coe := λ x y, mp y x }

lemma imp_self' (p : fml) : prf (p →' p) :=
mp (@axk p p) (mp axk axs)

lemma imp_comm {p q r : fml} (h : prf (p →' q →' r)) : prf (q →' p →' r) :=
mp axk (mp (mp (mp h axs) axk) (@axs _ (p →' q) _))

lemma imp_of_true (p : fml) {q : fml} (h : prf q) : prf (p →' q) :=
mp h axk

namespace prf
prefix `⊢ `:30 := prf

def mp' {p q} (h1 : ⊢ p →' q) (h2 : ⊢ p) : ⊢ q := mp h2 h1
def a1i {p q} : ⊢ p → ⊢ q →' p := mp' axk
def a2i {p q r} : ⊢ p →' q →' r → ⊢ (p →' q) →' p →' r := mp' axs
def con4i {p q} : ⊢ ¬' p →' ¬' q → ⊢ q →' p := mp' axX
def mpd {p q r} (h : ⊢ p →' q →' r) : ⊢ p →' q → ⊢ p →' r := mp' (a2i h)
def syl {p q r} (h1 : ⊢ p →' q) (h2 : ⊢ q →' r) : ⊢ p →' r := mpd (a1i h2) h1
def id {p} : ⊢ p →' p := mpd axk (@axk p p)
def a1d {p q r} (h : ⊢ p →' q) : ⊢ p →' r →' q := syl h axk
def com12 {p q r} (h : ⊢ p →' q →' r) : ⊢ q →' p →' r := syl (a1d id) (a2i h)
def con4d {p q r} (h : ⊢ p →' ¬' q →' ¬' r) : ⊢ p →' r →' q := syl h axX
def absurd {p q} : ⊢ ¬' p →' p →' q := con4d axk
def imidm {p q} (h : ⊢ p →' p →' q) : ⊢ p →' q := mpd h id
def contra {p} : ⊢ (¬' p →' p) →' p := imidm (con4d (a2i absurd))
def notnot2 {p} : ⊢ ¬' ¬' p →' p := syl absurd contra
def mpdd {p q r s} (h : ⊢ p →' q →' r →' s) : ⊢ p →' q →' r → ⊢ p →' q →' s := mpd (syl h axs)
def syld {p q r s} (h1 : ⊢ p →' q →' r) (h2 : ⊢ p →' r →' s) : ⊢ p →' q →' s := mpdd (a1d h2) h1
def con2d {p q r} (h1 : ⊢ p →' q →' ¬' r) : ⊢ p →' r →' ¬' q := con4d (syld (a1i notnot2) h1)
def con2i {p q} (h1 : ⊢ p →' ¬' q) : ⊢ q →' ¬' p := con4i (syl notnot2 h1)
def notnot1 {p} : ��� p →' ¬' ¬' p := con2i id

#reduce notnot2


infixr ` →' `:50 := imp -- right associative

prefix `¬' `:51 := fml.not

def p_of_p (p : fml) : prf (p →' p) :=
mp (@axk p p) (mp axk axs)

inductive consequence (G : list fml) : fml → Type
| axk (p q) : consequence (p →' q →' p)
| axs (p q r) : consequence $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axn (p q) : consequence $ ((¬'q) →' (¬'p)) →' p →' q
| mp (p q) : consequence p → consequence (p →' q) → consequence q
| of_G (g ∈ G) : consequence g

def consequence_of_thm (f : fml) (H : prf f) (G : list fml) : consequence G f :=
begin
  induction H,
  exact consequence.axk G H_p H_q,
  exact consequence.axs G H_p H_q H_r,
  exact consequence.axn G H_p H_q,
  exact consequence.mp H_p H_q H_ih_a H_ih_a_1,
end

def thm_of_consequence_null (f : fml) (H : consequence [] f) : prf f :=
begin
  induction H,
  exact @axk H_p H_q,
  exact @axs H_p H_q H_r,
  exact @axX H_p H_q,
  exact mp H_ih_a H_ih_a_1,
  exact false.elim (list.not_mem_nil H_g H_H),
end

def deduction (G : list fml) (p q : fml) (H : consequence (p :: G) q) : consequence G (p →' q) :=
begin
  induction H,
  have H1 := consequence.axk G H_p H_q,
  have H2 := consequence.axk G (H_p →' H_q →' H_p) p,
  exact consequence.mp _ _ H1 H2,
  have H6 := consequence.axs G H_p H_q H_r,
  have H7 := consequence.axk G ((H_p →' H_q →' H_r) →' (H_p →' H_q) →' H_p →' H_r) p,
  exact consequence.mp _ _ H6 H7,
  have H8 := consequence.axn G H_p H_q,
  have H9 := consequence.axk G (((¬' H_q) →' ¬' H_p) →' H_p →' H_q) p,
  exact consequence.mp _ _ H8 H9,
  have H3 := consequence.axs G p H_p H_q,
  have H4 := consequence.mp _ _ H_ih_a_1 H3,
  exact consequence.mp _ _ H_ih_a H4,
  rw list.mem_cons_iff at H_H,
  exact if h : H_g ∈ G then
  begin
    have H51 := consequence.of_G H_g h,
    have H52 := consequence.axk G H_g p,
    exact consequence.mp _ _ H51 H52,
  end else
  begin
    have h := H_H.resolve_right h,
    rw h,
    exact consequence_of_thm _ (p_of_p p) G,
  end
end

def part1 (p : fml) : consequence [¬' (¬' p)] p :=
begin
  have H1 := consequence.axk [¬' (¬' p)] p p,
  have H2 := consequence.axk [¬' (¬' p)] (¬' (¬' p)) (¬' (¬' (p →' p →' p))),
  have H3 := consequence.of_G (¬' (¬' p)) (list.mem_singleton.2 rfl),
  have H4 := consequence.mp _ _ H3 H2,
  have H5 := consequence.axn [¬' (¬' p)] (¬' p) (¬' (p →' p →' p)),
  have H6 := consequence.mp _ _ H4 H5,
  have H7 := consequence.axn [¬' (¬' p)] (p →' p →' p) p,
  have H8 := consequence.mp _ _ H6 H7,
  exact consequence.mp _ _ H1 H8,
end

def p_of_not_not_p (p : fml) : prf ((¬' (¬' p)) →' p) :=
begin
  have H1 := deduction [] (¬' (¬' p)) p,

  have H2 := H1 (part1 p),
  exact thm_of_consequence_null ((¬' (¬' p)) →' p) H2,
end

#reduce p_of_not_not_p
#reduce @notnot2

theorem not_not_p_of_p (p : fml) : prf (p →' (¬' (¬' p))) :=
begin
  have H1 := prf.axs p (¬' (¬' p)),
  have H2 := p_of_not_not_p (¬' p),
  exact thm.mp H2 H1,
end
set_option pp.implicit true
#reduce not_not_p_of_p

#exit
@[derive decidable_eq] inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:40 := fml.not

inductive prf : fml → Type
| axk (p q) : prf (p →' q →' p)
| axs (p q r) : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX (p q) : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

#print prf.rec

open prf

/-
-- example usage:
lemma p_of_p_of_p_of_q (p q : fml) : prf $ (p →' q) →' (p →' p) :=
begin
  apply mp (p →' q →' p) ((p →' q) →' p →' p) (axk p q),
  exact axs p q p
end
-/

def is_not : fml → Prop :=
λ f, ∃ g : fml, f = ¬' g

#print prf.rec_on
theorem Q6b (f : fml) (p : prf f) : is_not f → false :=
begin
  induction p,
  {admit},
  {admit},
  {admit},
  {
    clear p_ih_a_1,
    }


end

#print Q6b

theorem Q6b : ∀ p : fml, ¬(prf $ p →' ¬' ¬' p) :=
begin
  cases p,


end


#exit

import data.fintype

section

@[derive decidable_eq] inductive cbool
| t : cbool
| f : cbool
| neither : cbool
open cbool

instance : fintype cbool := ⟨{t,f,neither}, λ x, by cases x; simp⟩

variables (imp : cbool → cbool → cbool) (n : cbool → cbool)
  (a1 : ∀ p q, imp p (imp q p) = t)
  (a2 : ∀ p q, imp (imp (n q) (n p)) (imp p q) = t)
  (a3 : ∀ p q r, imp (imp p (imp q r)) (imp (imp p q) (imp p r)) = t)
include a1 a2 a3

set_option class.instance_max_depth 50

-- example : ∀ p, imp p (n (n p)) = t :=
-- by revert imp n; exact dec_trivial



#exit
import measure_theory.measure_space topology.metric_space.emetric_space

noncomputable lemma F {α β : Sort*} : ((α → β) → α) → α :=
classical.choice $ (classical.em (nonempty α)).elim
  (λ ⟨a⟩, ⟨λ _, a⟩)
  (λ h, ⟨λ f, false.elim (h ⟨f (λ a, false.elim (h ⟨a⟩))⟩)⟩)

#reduce F

def X {α : Type*} [add_monoid α] {p : α → Prop} [is_add_submonoid p]: add_monoid (subtype p) :=
subtype.add_monoid

instance add_monoid_integrable' [is_add_submonoid (ball (0 : ℝ) ⊤)]:
  add_monoid (subtype (ball (0 : ℝ) ⊤)) := X

#exit
import measure_theory.measurable_space

example {α : Type*} [add_monoid α] (p : set α): add_monoid (subtype p) := by apply_instance
#print topological_add_group
#eval ((univ : finset (perm (fin 7))).filter (λ x, sign x = 1 ∧ order_of x = 6)).card


import data.polynomial tactic.omega

open polynomial
set_option trace.simplify.rewrite true
example (x : ℤ) : x ^ 2 + x = x + x * x :=
by ring

example (a b c d e f : ℤ) (ha : a ≤ 2) (hb : c ≥ b - e) (hf : 5 * f - 2 * c = 9 * b - 7 * e)
  (hd : d + 3 ≤ 7 + e) : d + 3 ≤ 7 + e := by omega


open mv_polynomial
set_option trace.simplify.rewrite true
lemma z : (X () : mv_polynomial unit ℤ) ^ 2 = X () * X () :=
begin
  ring,

end
#print z

#exit
import tactic.omega

example (a b c : ℕ) (hab : 20 * a + 2 * b = 10 * b + c + 10 * c + a)
  (ha : a < 10) (hb : b < 10) (hc : c < 10) : a = b ∧ b = c :=
by omega

example : ∀ {a : ℕ} (ha : a < 10) {b : ℕ} (hb : b < 10) {c : ℕ} (hc : c < 10)
  (hab : 20 * a + 2 * b = 10 * b + c + 10 * c + a), a = b ∧ b = c :=
by omega


#exit
import data.equiv.algebra

variables {α : Type*} {β : Type*} [add_monoid β] (e : α ≃ β)

instance foo : add_monoid α := equiv.add_monoid e

--import tactic.omega
#exit
example (p q : ℕ → Prop) (h : p = q) (x : subtype p) :
  (eq.rec_on h x : subtype q) = ⟨x.1, h ▸ x.2⟩ :=
begin
  cases x, subst h,

end

def X : Type := ℤ

set_option trace.class_instances true
instance : comm_ring X := by apply_instance

lemma whatever (a b : ℕ) : a + b = 1 ↔ (a = 1 ∧ b = 0) ∨ (b = 1 ∧ a = 0) := by omega
#print whatever

example : 1000000 * 1000000 = 1000000000000 := by norm_num

lemma h (a b n : ℤ) : a + b - b + n = a + n := by simp

example : (1 : ℤ) + 2 - 2 + 3 = 1 + 3 := h 1 2 3

example : default Prop := trivial

inductive nat2
| zero : nat2
| succ : nat2 → nat2

#print nat2.zero
#print nat2.succ
#print nat2.rec

def add (a b : nat2) : nat2 :=
nat2.rec a (λ c, nat2.succ) b

example : ∀ (b : ℕ), b = b := by omega
example : ∃ (a : ℕ), a = 0 := by omega
example :

#print z

example : (∀ p q r : Prop, ((p ↔ q) ↔ r) ↔ (p ↔ (q ↔ r))) → ∀ p, p ∨ ¬p :=
λ h p, ((h (p ∨ ¬p) false false).mp
  ⟨λ h, h.mp (or.inr (λ hp, h.mp (or.inl hp))), false.elim⟩).mpr iff.rfl

noncomputable def step_fun : ℝ → ℝ := λ x, if x ≤ ξ then 1 else 0

lemma discont_at_step : ¬ (continuous_at step_fun ξ) :=
begin
  unfold continuous_at,
  -- our goal:
  -- ⊢ ¬filter.tendsto step_fun (nhds ξ) (nhds (step_fun ξ))
  rw metric.tendsto_nhds_nhds,
  push_neg,
  -- goal
  -- ∃ (ε : ℝ), ε > 0 ∧ ∀ (δ : ℝ), δ > 0 → (∃ {x : ℝ},
  -- dist x ξ < δ ∧ ε ≤ dist (step_fun x) (step_fun ξ))
  use 1,
  refine ⟨by norm_num, _⟩,
  assume δ δ0,
  use ξ + δ / 2,
  split,
  { simp [real.dist_eq, abs_of_nonneg (le_of_lt (half_pos δ0)), half_lt_self δ0] },
  { have : ¬ ξ + δ / 2 ≤ ξ, from not_le_of_gt ((lt_add_iff_pos_right _).2 (half_pos δ0)),
    simp [real.dist_eq, step_fun, le_refl, this] }
end


#exit
import data.set.basic data.finset

variables {α : Type*} {A B : set α}

theorem Q8: (A \ B) ∪ (B \ A) = (A ∪ B) \ (A ∩ B) :=
set.ext $ λ x, ⟨λ h, h.elim (λ h, ⟨or.inl h.1, mt and.right h.2⟩)
    (λ h, ⟨or.inr h.1, mt and.left h.2⟩),
  λ h, h.1.elim (λ hA, or.inl ⟨hA, λ hB, h.2 ⟨hA, hB⟩⟩)
    (λ hB, or.inr ⟨hB, λ hA, h.2 ⟨hA, hB⟩⟩)⟩

lemma f : has_sub (set α) := by apply_instance

#print f

#print axioms Q8
#print axioms

#exit
import set_theory.cardinal tactic.norm_num

def list_to_nat : list bool → nat
| [] := 0
| (ff :: l) := 3 ^ (list_to_nat l) + 1
| (tt :: l) := 3 ^ (list_to_nat l) + 2

lemma list_to_nat_injective : function.injective list_to_nat
| [] [] h := rfl
| (a::l) [] h := by cases a; exact nat.no_confusion h
| [] (a::l) h := by cases a; exact nat.no_confusion h
| (a::l₁) (b::l₂) h := begin
  cases a; cases b;
  dunfold list_to_nat at h,
  simp [pow_left_inj] at h,

end


noncomputable def list_unit_equiv_list_bool : list unit ≃ list bool :=
classical.choice $ quotient.exact $
show cardinal.mk (list unit) = cardinal.mk (list bool),
  begin
   rw [cardinal.mk_list_eq_sum_pow, cardinal.mk_list_eq_sum_pow],
   apply le_antisymm,
   { refine cardinal.sum_le_sum _ _ (λ _, cardinal.power_le_power_right $
       ⟨⟨λ _, tt, λ _ _ _, subsingleton.elim _ _⟩⟩), },
   { simp, }

end


#print nat.to_digits
#print nat.to_digi
def bool_to_unit : l :=


lemma injective_unit_to_bool : function.injective unit_to_bool
| [] [] h := rfl
| (x::l) [] h := by cases x; exact absurd h (list.cons_ne_nil _ _)
| [] (x::l) h := by cases x; exact absurd h (λ h, list.cons_ne_nil _ _ h.symm)
| (tt::l₁) (tt::l₂) h := begin
  unfold unit_to_bool at h,
  simp at h,
  rw injective_unit_to_bool h
end
| (ff::l₁) (ff::l₂) h := begin
  unfold unit_to_bool at h,
  simp at h,
  rw injective_unit_to_bool h
end
| (tt::l₁) (ff::l₂) h := begin
  unfold unit_to_bool at h,
  simp at h,
  rw ← unit_to_bool at h,
  have := injective_unit_to_bool h,
end

example : list unit ≃ list bool :=
#exit
import data.fintype
--set_option pp.all true
lemma fin_injective {n m : ℕ} (h : fin n = fin m) : n = m :=
have e : fin n ≃ fin m, by rw h,
by rw [← fintype.card_fin n, fintype.card_congr e, fintype.card_fin]

lemma h : ∀ n, su

#print (show ∀ n, (subsingleton (fin n)), by apply_instance)
instance gjh (α : Type*) : subsingleton (fintype α) :=
⟨λ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩, by congr⟩

#print fin_injective
#print axioms fintype.card_fin
#print axioms fin_injective
#exit
import data.real.basic data.set.intervals topology.basic analysis.complex.exponential
local attribute [instance] classical.prop_decidable

open real

noncomputable def fake_abs (x : ℝ) : ℝ := if x ≤ 0 then -x else x

noncomputable def fake_abs' : ℝ → ℝ := λ x, if x ≤ 0 then -x else x

#print prefix fake_abs.equations._eqn_1

#print prefix fake_abs'.equations._eqn_1

#exit
import set_theory.ordinal
universe u
open function lattice
theorem schroeder_bernstein {α β : Type*} {f : α → β} {g : β → α}
  (hf : injective f) (hg : injective g) : ∃h:α→β, bijective h :=
let s : set α := lfp $ λs, - (g '' - (f '' s)) in
have hs : s = - (g '' - (f '' s)) :=
begin
  dsimp [s, lfp, lattice.Inf, has_Inf.Inf,
    complete_lattice.Inf, set.mem_set_of_eq,
    set.image, set.compl, has_le.le,
    preorder.le, partial_order.le, order_bot.le,
    bounded_lattice.le, complete_lattice.le, has_neg.neg,
    boolean_algebra.neg, complete_boolean_algebra.neg,
    set.subset_def],
  simp only [not_exists, classical.not_forall, not_and, set.ext_iff,
    set.mem_set_of_eq], intro,
  split; finish

  --simp at hs,

end, sorry

open function

lemma injective_of_increasing {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) [is_trichotomous α r]
  [is_irrefl β s] (f : α → β) (hf : ∀{x y}, r x y → s (f x) (f y)) : injective f :=
begin
  intros x y hxy,
  rcases trichotomous_of r x y with h | h | h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this,
  exact h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this
end

def well_order {α : Type*} : α → α → Prop := classical.some (@well_ordering_thm α)

def wf {α : Type*} : has_well_founded α :=
⟨well_order, (classical.some_spec (@well_ordering_thm α)).2⟩

open cardinal

local attribute [instance] wf
variable {α : Type u}
local infix ` ≺ `:50 := well_order

instance is_well_order_wf : is_well_order _ ((≺) : α → α → Prop) :=
classical.some_spec (@well_ordering_thm α)

noncomputable def to_cardinal {α : Type u} : α → cardinal.{u}
| a := cardinal.succ (@cardinal.sup.{u u} {y : α // y ≺ a}
   (λ y, have y.1 ≺ a, from y.2, to_cardinal y.1))
using_well_founded {dec_tac := tactic.assumption }

local attribute [instance] classical.dec
#print cardinal
lemma to_cardinal_increasing : ∀ {x y : α} (h : x ≺ y), to_cardinal x < to_cardinal y
| a b hab :=
have ha' : a = (show subtype (≺ b), from ⟨a, hab⟩).1, by simp,
begin
  conv {to_rhs, rw [to_cardinal], congr, congr, funext, rw to_cardinal },
  rw [to_cardinal, cardinal.lt_succ],
  have ha' : a = (show subtype (≺ b), from ⟨a, hab⟩).1, by simp,
  rw ha',
  exact le_sup _ _
end

lemma to_cardinal_injective : function.injective (@to_cardinal α) :=
injective_of_increasing (≺) (<) _ (λ _ _, to_cardinal_increasing)

def to_Type : α → Type u :=
quotient.out ∘ to_cardinal

#print to_Type

lemma injective_to_Type : function.injective (@to_Type α) :=
function.injective_comp (λ x y h, by convert congr_arg cardinal.mk h; simp)
  to_cardinal_injective

lemma Type_gt : (Type u ↪ α) → false :=
λ ⟨f, h⟩, cantor_injective (f ∘ @to_Type (set α))
  (function.injective_comp h injective_to_Type)

lemma universe_strict_mono : (Type (u+1) ↪ Type u) → false := Type_gt

lemma universe_strict_mono' : Type u ↪ Type (u+1) :=
⟨_, injective_to_Type⟩
--#print embedding.trans
example : cardinal.lift.{(u+1) (u+2)} (cardinal.mk (Type u)) <
  cardinal.mk (Type (u+1)) :=
lt_of_not_ge (λ ⟨f⟩, universe_strict_mono
  (f.trans ⟨ulift.down, λ ⟨_⟩ ⟨_⟩ h, congr_arg _ h⟩))

-- lemma injective_of_increasing {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) [is_trichotomous α r]
--   [is_irrefl β s] (f : α → β) (hf : ∀{x y}, r x y → s (f x) (f y)) : injective f :=
-- begin
--   intros x y hxy,
--   rcases trichotomous_of r x y with h | h | h,
--   have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this,
--   exact h,
--   have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this
-- end

-- def well_order {α : Type*} : α → α → Prop := classical.some (@well_ordering_thm α)

-- def wf {α : Type*} : has_well_founded α :=
-- ⟨well_order, (classical.some_spec (@well_ordering_thm α)).2⟩

-- open cardinal

-- local attribute [instance] wf
-- variable {α : Type u}
-- local infix ` ≺ `:50 := well_order

-- instance is_well_order_wf : is_well_order _ ((≺) : α → α → Prop) :=
-- classical.some_spec (@well_ordering_thm α)

-- noncomputable def to_cardinal {α : Type u} : α → cardinal.{u}
-- | a := cardinal.succ (@cardinal.sup.{u u} {y : α // y ≺ a}
--    (λ y, have y.1 ≺ a, from y.2, to_cardinal y.1))
-- using_well_founded {dec_tac := tactic.assumption }

-- local attribute [instance] classical.dec

-- lemma to_cardinal_increasing : ∀ {x y : α} (h : x ≺ y), to_cardinal x < to_cardinal y
-- | a b hab :=
-- have ha' : a = (show subtype (≺ b), from ⟨a, hab⟩).1, by simp,
-- begin
--   conv {to_rhs, rw [to_cardinal], congr, congr, funext, rw to_cardinal },
--   rw [to_cardinal, cardinal.lt_succ],
--   have ha' : a = (show subtype (≺ b), from ⟨a, hab⟩).1, by simp,
--   rw ha',
--   exact le_sup _ _
-- end

-- lemma to_cardinal_injective : function.injective (@to_cardinal α) :=
-- injective_of_increasing (≺) (<) _ (λ _ _, to_cardinal_increasing)

-- def to_Type : α → Type u :=
-- quotient.out ∘ to_cardinal

-- lemma injective_to_Type : function.injective (@to_Type α) :=
-- function.injective_comp (λ x y h, by convert congr_arg cardinal.mk h; simp)
--   to_cardinal_injective

-- lemma Type_gt : (Type u ↪ α) → false :=
-- λ ⟨f, h⟩, cantor_injective (f ∘ @to_Type (set α))
--   (function.injective_comp h injective_to_Type)

-- lemma universe_strict_mono : (Type (u+1) ↪ Type u) → false := Type_gt


#exit
inductive foo: ℕ → ℕ → Type
def foo_fn (n m: ℕ): Type := foo n m → foo n m

inductive is_foo_fn
  : Π {n m: ℕ}, foo_fn n m → Type
| IsFooEta:
  Π {n m: ℕ} {f: foo_fn n m},
  is_foo_fn f
→ is_foo_fn (λ M, f M)
open is_foo_fn

def ext: -- equation compiler failed to prove equation lemma (
 -- workaround: disable lemma generation using `set_option eqn_compiler.lemmas false`)
    Π {n m: ℕ}
      {f: foo_fn n m},
    is_foo_fn f
  → Σ f': foo_fn n m, is_foo_fn f'
| _ _ _ (IsFooEta f) :=
  ⟨_, IsFooEta (ext f).snd⟩

set_option trace.simp_lemmas
def ext2: -- equation compiler failed to prove equation lemma
--(workaround: disable lemma generation using `set_option eqn_compiler.lemmas false`)
    Π {m n : ℕ}
      {f: foo_fn n m},
    is_foo_fn f
  → Σ f': foo_fn n m, is_foo_fn f'
| _ _ _ (IsFooEta f) :=
  ⟨_, IsFooEta (ext2 f).snd⟩

#print ext2._main

example : ∀ (n m : ℕ) (z : foo_fn n m) (f : is_foo_fn z),
  ext2 (IsFooEta f) = ⟨λ (M : foo n m), (ext2 f).fst M, IsFooEta ((ext2 f).snd)⟩ :=
λ _ _ _ _, rfl

#print ext.equations._eqn_1

#exit
import data.finset data.fintype

variables {α : Type*} {β : Type*}
@[instance] lemma nat.cast_coe : has_coe nat string := sorry
local attribute [-instance] nat.cast_coe

def embeddings [decidable_eq α] [decidable_eq β] :
  Π (l : list α), list β → list (Π a : α, a ∈ l → β)
| []     l   := [λ _ h, false.elim h]
| (a::l) []  := []
| (a::l₁) l₂ := (embeddings l₁ l₂).bind
  (λ f, (l₂.filter (λ b, ∀ a h, f a h ≠ b)).map
    (λ b a' ha', if h : a' = a then b else _))

#eval (embeddings [1,2,3,4,5] [1,2,3,4,5]).length
#eval 5^5
lemma card_embeddings :

#exit
import tactic

#print prod.lex

example {α : Type*} [preorder α] {x y : α × α}: prod.lex ((<) : α → α → Prop) (≤) x y
  ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2) :=
begin
  split,
  { assume h,
    { induction h;simp * at * } },
  { assume h,
    cases x, cases y,
    cases h,
    refine prod.lex.left _ _ _ h,
    dsimp at h,
    rw h.1,
    refine prod.lex.right _ _ h.2 }

end
example {α : Type*} {β : α → Type*} [preorder α] [Π a : α, preorder (β a)]
  {x y : psigma β} : psigma.lex (<) (λ a : α, @has_le.le (β a) _) x y
  ↔ x.1 < y.1 ∨ ∃ p : x.1 = y.1, x.2 ≤ by convert y.2 :=
begin
  split,
  { assume h,
    induction h; simp [*, eq.mpr] at * },
  { assume h, cases x, cases y,
    cases h,
    refine psigma.lex.left _ _ _ h,
    cases h,
    dsimp at h_w,
    subst h_w,
    refine psigma.lex.right _ _ h_h }
end

#exit
import tactic.interactive

def f {α : Type*} [decidable_eq α] (x y : α) : bool := x = y

local attribute [instance, priority 0] classical.prop_decidable

example {α : Type*} {P : Prop} {x y : α} (hxy : f x y = tt)
  (hP : f x y = tt → P) : P :=
by tauto!

#exit
import topology.metric_space.basic

def inclusion {α : Type*} {s t : set α} (h : s ⊆ t) : s → t :=
λ x : s, (⟨x, h x.2⟩ : t)

@[simp] lemma inclusion_self {α : Type*} {s : set α} (h : s ⊆ s) (x : s) :
  inclusion h x = x := by cases x; refl

@[simp] lemma inclusion_inclusion {α : Type*} {s t u : set α} (hst : s ⊆ t) (htu : t ⊆ u)
  (x : s) : inclusion htu (inclusion hst x) = inclusion (set.subset.trans hst htu) x :=
by cases x; refl

lemma inclusion_injective {α : Type*} {s t : set α} (h : s ⊆ t) :
  function.injective (inclusion h)
| ⟨_, _⟩ ⟨_, _⟩ := subtype.ext.2 ∘ subtype.ext.1

example {α : Type*} [topological_space α] (s t : set α) (h : s ⊆ t) :
  continuous (inclusion h) :=
continuous_subtype_mk

#exit
import algebra.associated

#print irreducible
]


end⟩

#print prime

#exit
example : ∃ h : 1 = 1, true := dec_trivial

#exit
import topology.basic data.set.intervals analysis.exponential
open real set

-- Give a handle on the set [0,1] ⊂ ℝ
def unit_interval := (Icc (0:ℝ) 1)
-- Define an identity function on the subtype corresponding to this set
def restricted_id := function.restrict (λ (x:ℝ), x) unit_interval

-- show that restricted_id is continuous
lemma cont_restricted_id : continuous restricted_id :=
begin
intro,
intro,
apply continuous_subtype_val _,
exact a,
end
-- main idea: "getting the value of the subtype" unifies with "restricted_id"

-- now show that the identity function (on ℝ) is continuous on the unit interval
lemma continuous_on_unit_interval_id : continuous_on (λ (x:ℝ), x) unit_interval :=
begin
rw [continuous_on_iff_continuous_restrict],
exact cont_restricted_id,
end

-- This breaks for 1/x, obviously.
-- First of all, we can't just use subtype.val, since that won't unify.
-- To get some hope that it will go through thing, let's start over with the interval (0,1].
def ounit_interval := (Ioc (0:ℝ) 1)

noncomputable def restricted_inv := function.restrict (λ (x:ℝ), 1/x) ounit_interval

lemma cont_restricted_inv : continuous restricted_inv :=
begin
  unfold restricted_inv function.restrict,
  simp only [one_div_eq_inv],
  exact continuous_inv (λ a, (ne_of_lt a.2.1).symm) continuous_subtype_val,
end
#print real.uniform_continuous_inv
#exit

open nat
#eval gcd (gcd (61 ^ 610 + 1) (61 ^ 671 - 1) ^ 671 + 1)
  (gcd (61 ^ 610 + 1) (61 ^ 671 - 1) ^ 610 - 1) % 10

example : gcd (gcd (61 ^ 610 + 1) (61 ^ 671 - 1) ^ 671 + 1)
  (gcd (61 ^ 610 + 1) (61 ^ 671 - 1) ^ 610 - 1) % 10 = 3 :=
begin


end

#exit
import tactic.ring data.real.basic algebra.module
example (x : ℝ) : x=2 → 2+x=x+2 := begin intro h, ring, end -- works
example (x : ℝ) : x=2 → 2*x=x*2 := begin intro h, ring, end -- works
example (x y : ℝ) : (x - y) ^ 3 = x^3 - 3 * x^2 * y + 3 * x * y^2 - y^3 := by ring

#print semimodule
constant r : ℕ → ℕ → Prop
notation a ` ♥ `:50 b :50:= r b a
infix ` ♠ ` : 50 := r
#print notation ♥
example (a b : ℕ) : a ♥ b :=
begin
/-
1 goal
a b : ℕ
⊢ b ♠ a
-/
end


#exit
import tactic.norm_num data.zmod.basic



#print X

example : ∀ (x y z : zmod 9), x^3 + y^3 + z^3 ≠ 4 := dec_trivial


#exit
import analysis.normed_space.basic

variable {Β : Type*}

namespace hidden

@[simp] lemma norm_mul [normed_field-eq B] (a b : Β) : ∥a * b∥ = ∥a∥ * ∥b∥ :=
normed_field.norm_mul a b

instance normed_field.is_monoid_hom_norm [normed_field α] : is_monoid_hom (norm : α → ℝ) :=
⟨norm_one, norm_mul⟩

@[simp] lemma norm_pow [normed_field α] : ∀ (a : α) (n : ℕ), ∥a^n∥ = ∥a∥^n :=
is_monoid_hom.map_pow norm

end hidden

#exit
import tactic.norm_num

def FP_step : ℕ × ℕ → ℕ × ℕ :=
 λ ⟨a,b⟩, ⟨b,(a + b) % 89⟩

def FP : ℕ → ℕ × ℕ
| 0 := ⟨0,1⟩
| (n + 1) := FP_step (FP n)

def F (n : ℕ) : ℕ := (FP n).fst

lemma FP_succ {n a b c : ℕ}
  (h : FP n = (a, b)) (h2 : (a + b) % 89 = c) : FP (nat.succ n) = (b, c) :=
by rw [← h2, FP, h]; refl
set_option pp.max_steps 1000000000
set_option pp.max_depth 1000000000

lemma L : F 44 = 0 := begin
  have : FP 0 = (0, 1) := rfl,
  iterate 44 { replace := FP_succ this (by norm_num; refl) },
  exact congr_arg prod.fst this
end

lemma zero_eq_one : 0 = @has_zero.zero ℕ ⟨1⟩ :=
begin
  refl,
end

#print L

#exit
--import data.zmod.basic

lemma double_neg_em : (∀ p, ¬¬p → p) ↔ (∀ p, p ∨ ¬p) :=
⟨λ dneg p, dneg (p ∨ ¬ p) (λ h, h (or.inr (h ∘ or.inl))),
λ em p hneg, (em p).elim id (λ h, (hneg h).elim)⟩
#print or.assoc
lemma z : (∀ {α : Type} {p : α → Prop}, (∀ x, p x) ↔ ∄ x, ¬ p x) → ∀ (P : Prop), P ∨ ¬ P :=
λ h P, (@h unit (λ _, P ∨ ¬ P)).2 (λ ⟨_, h⟩, h (or.inr (h ∘ or.inl))) ()
#print axioms z

lemma y : (7 + 8) + 5 = 7 + (8 + 5) :=
add_assoc 7 8 5
#print axioms nat.mul_assoc
#reduce y

example : 0 = @has_zero.zero ℕ ⟨1⟩ :=
begin
  refl,

end

example : (⊥ : ℕ) = @lattice.has_bot.bot ℕ ⟨1⟩ :=
begin
  refl,

end


lemma b {m n : ℕ} : (m * n) % n = 0 :=
nat.mul_mod_left _ _


lemma iff_assoc {p q r : Prop} : p ↔ (q ↔ r) ↔ (p ↔ q ↔ r) := by tauto!

#print iff_assoc

lemma eq_assoc {p q r : Prop} : p = (q = r) = (p = q = r) :=
by simpa [iff_iff_eq] using iff.assoc

#print iff_assoc
#reduce iff.assoc

example {p q : Prop} : (p ↔ p ∧ q) ↔ (p → q) :=
by split; intros; simp * at *

#exit
import data.real.basic

example : (2 : ℝ) ≤ ((((2 - (157 / 50 / 2 ^ (4 + 1)) ^ 2) ^ 2 - 2) ^ 2 - 2) ^ 2 - 2) ^ 2 :=
begin
  rw (show 4 + 1 = 5, from rfl),
  rw (show (2 : ℝ) ^ 5 = 32, by norm_num),
  rw (show (157 : ℝ) / 50 / 32 = 157 / 1600, by norm_num),
  rw (show ((157 : ℝ) / 1600) ^ 2 = 24649 / 2560000, by norm_num),
  rw (show (2 : ℝ) - 24649 / 2560000 = 5095351/2560000, by norm_num),
  rw (show ((5095351 : ℝ) /2560000) ^ 2 = 25962601813201/6553600000000, by norm_num),
  -- let's try skipping steps
  rw (show ((((25962601813201 : ℝ) / 6553600000000 - 2) ^ 2 - 2) ^ 2 - 2) ^ 2 =
    6806775565993596917798714352237438749189222725565123913061124308255143227446400872965401873904861225601/3402823669209384634633746074317682114560000000000000000000000000000000000000000000000000000000000000000,
    by norm_num),
  -- worked!
  -- ⊢ 2 ≤
  --  6806775565993596917798714352237438749189222725565123913061124308255143227446400872965401873904861225601 /
  --    3402823669209384634633746074317682114560000000000000000000000000000000000000000000000000000000000000000
  rw le_div_iff,
  { norm_num },
  { norm_num }
  -- ⊢ 0 < 3402823669209384634633746074317682114560000000000000000000000000000000000000000000000000000000000000000

end


import algebra.big_operators data.int.basic

open finset nat
variables {α : Type*} [semiring α]
--set_option trace.simplify.rewrite true

lemma nat.sub_right_inj {a b c : ℕ} (h₁ : c ≤ a) (h₂ : c ≤ b) : a - c = b - c ↔ a = b :=
by rw [nat.sub_eq_iff_eq_add h₁, nat.sub_add_cancel h₂]

lemma lemma1 {x y z : ℕ → α} (n : ℕ) : (range (n + 1)).sum
  (λ i, (range (i + 1)).sum (λ j, x j * y (i - j)) * z (n - i)) =
  (range (n + 1)).sum (λ i, x i * (range (n - i + 1)).sum (λ j, y j * z (n - i - j))) :=
begin
  induction n,
  { simp [mul_assoc] },
  { simp [*, mul_assoc, @range_succ (succ n_n)] at * }
end

#print imp_congr_ctx
#print lemma1

#exit
import algebra.group data.equiv.basic

variables {α : Type*} {β : Type*}

structure monoid_equiv (α β : Type*) [monoid α] [monoid β] extends α ≃ β :=
(mul_hom : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

infix ` ≃ₘ ` : 50 := monoid_equiv

instance sfklkj [monoid α] [monoid β] (f : α ≃ₘ β) : is_monoid_hom f.to_fun :=
{ map_mul := f.mul_hom,
  map_one := calc f.to_equiv.to_fun 1
    = f.to_equiv.to_fun 1 * f.to_equiv.to_fun (f.to_equiv.inv_fun 1) :
      by rw [f.to_equiv.right_inv, mul_one]
    ... = 1 : by rw [← f.mul_hom, one_mul, f.to_equiv.right_inv] }

#exit
import data.multiset


open nat

def S : multiset ℕ := quot.mk _ [1,2]

def T : multiset ℕ := quot.mk _ [2,1]

lemma S_eq_T : S = T := quot.sound (list.perm.swap _ _ _)

def X (m : multiset ℕ) : Type := {n : ℕ // n ∈ m}

def n : X S := ⟨1, dec_trivial⟩

def n' : X T := eq.rec_on S_eq_T n
set_option pp.proofs true
#reduce n'

def id' (n : ℕ) : ℕ := pred (1 + n)

lemma id'_eq_id : id' = id := funext $ λ _, by rw [id', add_comm]; refl

def Y (f : ℕ → ℕ) : Type := {n : ℕ // f n = n}

def m : Y id := ⟨0, rfl⟩

def m' : Y id' := eq.rec_on id'_eq_id.symm m
set_option pp.proofs true
#reduce m'

import topology.metric_space.basic tactic.find
open filter
universes u v
variables {ι : Type u} {α : ι → Type v} [fintype ι] [∀ i, metric_space (α i)]

#print function.inv_fun

lemma g : lattice.complete_lattice Prop := by apply_instance
#print lattice.complete_lattice_Prop
lemma h :
  (⨅ (ε : ℝ) (h : ε > 0), principal {p : (Π i, α i) × (Π i, α i) | dist p.1 p.2 < ε} =
  ⨅ i : ι, filter.comap (λ a : (Π i, α i)×(Π i, α i), (a.1 i, a.2 i)) uniformity)
  =
  ∀ (ε : ℝ) (h : ε > 0), principal {p : (Π i, α i) × (Π i, α i) | dist p.1 p.2 < ε} =
  ⨅ i : ι, filter.comap (λ a : (Π i, α i)×(Π i, α i), (a.1 i, a.2 i)) uniformity :=
by simp [lattice.infi_Prop_eq]

#exit

--local attribute [semireducible] reflected
#print char.to_nat
#print string.to_nat
#eval "∅".front.to_nat

#eval (⟨11, dec_trivial⟩ : char)
#eval "∅".front.to_nat - "/".front.to_nat
#eval 8662 - 8192 - 256 - 128 - 64 - 16 - 4 - 2
#eval "/".front.to_nat

meta def f (n : ℕ) (e : expr): expr :=
`(nat.add %%e %%`(n))

def g : ℕ := by tactic.exact (f 5 `(1))
#print int
#eval g

def foo : bool → nat → bool
| tt 0     := ff
| tt m     := tt
| ff 0     := ff
| ff (m+1) := foo ff m

#print prefix foo
#print reflect
#eval foo tt 1


#exit
import topology.metric_space.basic
open nat
structure aux : Type 1 :=
(space  : Type)
(metric : metric_space space)

set_option eqn_compiler.zeta true

noncomputable def my_def (X : ℕ → Type) [m : ∀n, metric_space (X n)] : ∀n:ℕ, aux
| 0 :=
  { space := X 0,
    metric := by apply_instance }
| (succ n) :=
  { space := prod (my_def n).space (X n.succ),
    metric := @prod.metric_space_max _ _ (my_def n).metric _ }

#print prefix my_def
set_option pp.all true
#print my_def._main

example : ∀ (X : nat → Type) [m : Π (n : nat), metric_space.{0} (X n)] (n : nat),
  @eq.{2} aux (@my_def._main X m (nat.succ n))
    {space := prod.{0 0} ((@my_def._main X m n).space) (X (nat.succ n)),
     metric := @prod.metric_space_max.{0 0} ((@my_def._main X m n).space) (X (nat.succ n))
                 ((@my_def._main X m n).metric)
                 (m (nat.succ n))} :=
  λ _ _ _, by tactic.reflexivity tactic.transparency.all

example : ∀ (X : nat → Type) [m : Π (n : nat), metric_space.{0} (X n)] (n : nat),
  @eq.{2} aux {space := prod.{0 0} ((@my_def._main X m n).space) (X (nat.succ n)),
     metric := @prod.metric_space_max.{0 0} ((@my_def._main X m n).space) (X (nat.succ n))
                 ((@my_def._main X m n).metric)
                 (m (nat.succ n))}
{space := prod.{0 0} ((@my_def X m n).space) (X (nat.succ n)),
     metric := @prod.metric_space_max.{0 0} ((@my_def X m n).space) (X (nat.succ n))
     ((@my_def X m n).metric)
                 (m (nat.succ n))} := λ _ _ _, rfl
example : my_def = my_def._main := rfl

lemma b : ∀ (X : nat → Type) [m : Π (n : nat), metric_space.{0} (X n)] (n : nat),
  @eq.{2} aux
    {space := prod.{0 0} ((@my_def X m n).space) (X (nat.succ n)),
     metric := @prod.metric_space_max.{0 0} ((@my_def X m n).space) (X (nat.succ n))
     ((@my_def X m n).metric)
                 (m (nat.succ n))}
    (@my_def X m (nat.succ n))
  := λ _ _ _, by tactic.reflexivity tactic.transparency.all

example (X : ℕ → Type) [m : ∀n, metric_space (X n)] (n : ℕ) :
  my_def X (n+1) = ⟨(my_def X n).space × (X n.succ),
    @prod.metric_space_max.{0 0} _ _ (my_def X n).metric _⟩ :=
by refl

#print my_def._main
#exit
import tactic

class A (α : Type*) :=
(a : α)

class B (α : Type*) extends A α :=
(b : α)

class C (α : Type*) :=
(a : α)
(t : true)

instance C.to_A (α : Type*) [C α] : A α :=
{ ..show C α, by apply_instance }

instance B.to_C {α : Type*} [B α] : C α :=
{ t := trivial, .. show B α, by apply_instance }

def B.to_A' (α : Type*) [n : B α] : A α :=
A.mk (B.to_A α).a

def a' {α : Type*} [A α] := A.a α

example {α : Type*} [n : B α] (x : α) (h : @a' _ (B.to_A α) = x) : @a' _ (C.to_A α) = x :=
by rw h


namespace foo
open classical

local attribute [instance] classical.prop_decidable
@[derive decidable_eq] inductive value : Type

@[derive decidable_eq] structure foo :=
(bar : ℕ)

end foo

#exit
example {p : Prop} : (∀ q, (p → q) → q) → p :=
λ h, classical.by_contradiction (h false)


import logic.function data.quot data.set.basic
universe u
inductive tree_aux (α : Type u) : bool → Type u
| nil : tree_aux ff
| cons : α → tree_aux ff → tree_aux ff
| mk_tree : α → tree_aux ff → tree_aux tt


variables (α : Type*) (β : Type*) (γ : Type*) (δ : Type*)

open function

example {p q : Prop} (h : p → q) : ¬q → ¬p := (∘ h)

#check ((∘) ∘ (∘)) not eq
#reduce (λ (x : α → β) (y : δ → γ → α) (z : δ) (w : γ), ((∘) ∘ (∘)) x y z w)

def fun_setoid {α β} (f : α → β) : setoid α :=
{ r := (∘ f) ∘ eq ∘ f,
  iseqv := ⟨λ _, rfl, λ _ _, eq.symm, λ _ _ _, eq.trans⟩ }

#reduce (λ f : α → β, ((∘ f) ∘ eq ∘ f))

structure quotient_map (α β : Type*) :=
(to_fun : α → β)
(inv_fun : β → quotient (fun_setoid to_fun))
(right_inverse : right_inverse inv_fun
  (λ a : quotient (fun_setoid to_fun), quotient.lift_on' a to_fun (λ _ _, id)))

example {α : Type*} [s : setoid α] : quotient_map α (quotient s) :=
{ to_fun := quotient.mk,
  inv_fun := λ a, quotient.lift_on a (λ a, (quotient.mk' a : quotient (fun_setoid quotient.mk)))
    (λ a b h, quotient.sound' (quotient.sound h)),
  right_inverse := λ x, quotient.induction_on x (λ _, rfl) }



#exit
import topology.metric_space.isometry

variables {X : Type*} {Y : Type*} [metric_space X] [metric_space Y] (i : X ≃ᵢ Y)
open metric

def jaih : bool := true

#print jaih
#print to_bool

#print (true : bool)

#exit
import logic.function

universes u v
axiom choice : Π (α : Sort u), nonempty (nonempty α → α)
∈
example : nonempty (Π {α : Sort u}, nonempty α → α) :=
let ⟨x⟩ := choice (Σ' α : Sort u, nonempty α) in
have _ := x _,
⟨_⟩
#reduce function.cantor_surjective
#exit
import topology.continuity
open set
variables {X : Type*} {Y : Type*} [topological_space X] [topological_space Y]
#print prod.topological_space
#print topological_space.generate_open
#reduce (@prod.topological_space X Y _ _).is_open
def prod_topology : topological_space (X × Y) :=
{ is_open := λ R, ∃ S : set (set (X × Y)), R = ⋃₀ S ∧
    ∀ s ∈ S, ∃ (U : set X) (hU : is_open U) (V : set Y) (hV : is_open V), s = set.prod U V,
  is_open_univ := sorry,
  is_open_inter := sorry,
  is_open_sUnion := sorry }
example : @prod_topology X Y _ _ = prod.topological_space := rfl
attribute [instance, priority 1000] prod_topology

example (U : set X) (V : set Y) : set.prod U V = prod.fst ⁻¹' U ∩ prod.snd ⁻¹' V := rfl
#print topolog
example {Z : Type*}[topological_space Z]
  (f : Z → X × Y) (hX : continuous (prod.fst ∘ f)) (hY : continuous (prod.snd ∘ f)) :
  continuous f :=
λ S ⟨T, hT⟩, begin
  rw [hT.1, preimage_sUnion],
  refine is_open_Union (λ s, is_open_Union (λ hs, _)),
  rcases hT.2 s hs with ⟨U, hU, V, hV, hUV⟩,
  rw hUV,
  show is_open (((prod.fst ∘ f)⁻¹' U) ∩ (prod.snd ∘ f)⁻¹' V),
  exact is_open_inter (hX _ hU) (hY _ hV)
end

example {X Y: Type*} [topological_space X] [topological_space Y]
  (f : X → Y) (hf : continuous f) (V : set Y) : is_closed V → is_closed (f ⁻¹' V) :=
hf _

#print set.prod
#print has_seq
example {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
  (f : Z → X × Y) (hX : continuous (prod.fst ∘ f)) (hY : continuous (prod.snd ∘ f)) :
  continuous f :=
λ S hS, begin
  rw is_open_prod_iff at hS,


end
#print g

#exit
import data.complex.exponential analysis.exponential algebra.field topology.algebra.topological_structures

open real

theorem continuous_cos_x_plus_x : continuous (λ x, cos x + x) :=
continuous_add real.continuous_cos continuous_id

theorem continuous_cos_x_plus_x' : continuous (λ x, cos x + x) :=
begin
 refine continuous_add _ _,
 exact continuous_cos,
 exact continuous_id,
end

namespace nzreal

def nzreal := {r : ℝ // r ≠ 0}
notation `ℝ*` := nzreal
constants nzc nzd : nzreal

-- one_ne_zero is zero_ne_one backwards
instance nzreal.one : has_one nzreal := ⟨⟨(1:ℝ), one_ne_zero⟩⟩

noncomputable instance nzreal.div : has_div nzreal :=
 ⟨λ q r, ⟨q.val / r.val, div_ne_zero q.property r.property⟩⟩

def nzreal_to_real (z : nzreal) : ℝ := subtype.val z
instance : has_lift nzreal real := ⟨nzreal_to_real⟩

class real.nzreal (r : ℝ) :=
(p : ℝ*)
(pf : r = ↑p)

-- idea is copied from data.real.nnreal
instance : has_coe ℝ* ℝ := ⟨subtype.val⟩

-- copy from Kevin Buzzard post on "computable division by non-zero real"
noncomputable instance : topological_space ℝ* := by unfold nzreal; apply_instance

end nzreal

-- almost the same as the proof for continuity of tangent
theorem continuous_1_over_x : continuous (λ (x : ℝ*), 1/x) :=
continuous_subtype_mk _ $ continuous_mul
  (continuous_subtype_val.comp continuous_const)
  (continuous_inv subtype.property
    (continuous_subtype_val.comp continuous_id))

#exit
import data.complex.basic

example {z : ℂ} :

#exit
import ring_theory.unique_factorization_domain

namespace hidden

constant α : Type

@[instance] constant I : integral_domain α

@[elab_as_eliminator] axiom induction_on_prime {P : α → Prop}
  (a : α) (h₁ : P 0) (h₂ : ∀ x : α, is_unit x → P x)
  (h₃ : ∀ a p : α, a ≠ 0 → prime p → P a → P (p * a)) : P a

local infix ` ~ᵤ ` : 50 := associated

#print associated

lemma factors_aux (a : α) : a ≠ 0 → ∃ s : multiset α, a ~ᵤ s.prod ∧ ∀ x ∈ s, irreducible x :=
induction_on_prime a (by simp)
  (λ x hx hx0, ⟨0, by simpa [associated_one_iff_is_unit]⟩)
  (λ a p ha0 hp ih hpa0, let ⟨s, hs₁, hs₂⟩ := ih ha0 in
    ⟨p :: s, by rw multiset.prod_cons;
      exact associated_mul_mul (associated.refl p) hs₁,
    λ x hx, (multiset.mem_cons.1 hx).elim (λ hxp, hxp.symm ▸ irreducible_of_prime hp) (hs₂ _)⟩)

@[simp] lemma mul_unit_dvd_iff {a b : α} {u : units α} : a * u ∣ b ↔ a ∣ b :=
⟨λ ⟨d, hd⟩, by simp [hd, mul_assoc], λ ⟨d, hd⟩, ⟨(u⁻¹ : units α) * d, by simp [mul_assoc, hd]⟩⟩

lemma dvd_iff_dvd_of_rel_left {a b c : α} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c :=
let ⟨u, hu⟩ := h in hu ▸ mul_unit_dvd_iff.symm

@[simp] lemma dvd_mul_unit_iff {a b : α} {u : units α} : a ∣ b * u ↔ a ∣ b :=
⟨λ ⟨d, hd⟩, ⟨d * (u⁻¹ : units α), by simp [(mul_assoc _ _ _).symm, hd.symm]⟩,
  λ h, dvd.trans h (by simp)⟩

lemma dvd_iff_dvd_of_rel_right {a b c : α} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c :=
let ⟨u, hu⟩ := h in hu ▸ dvd_mul_unit_iff.symm

lemma ne_zero_iff_of_associated {a b : α} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 :=
⟨λ ha, let ⟨u, hu⟩ := h in hu ▸ mul_ne_zero ha (units.ne_zero _),
  λ hb, let ⟨u, hu⟩ := h.symm in hu ▸ mul_ne_zero hb (units.ne_zero _)⟩



lemma irreducible_of_associated {p q : α} (h : irreducible p) :
  p ~ᵤ q → irreducible q :=
λ ⟨u, hu⟩, ⟨_, _⟩

lemma prime_of_irreducible {p : α} : irreducible p → prime p :=
induction_on_prime p (by simp) (λ p hp h, (h.1 hp).elim)
  (λ a p ha0 hp ih hpa, (hpa.2 p a rfl).elim (λ h, (hp.2.1 h).elim)
    (λ ⟨u, hu⟩, prime_of_associated hp ⟨u, hu ▸ rfl⟩))
#print multiset.prod
local attribute [instance] classical.dec

lemma multiset.dvd_prod {a : α} {s : multiset α} : a ∈ s → a ∣ s.prod :=
quotient.induction_on s (λ l a h, by simpa using list.dvd_prod h) a

lemma exists_associated_mem_of_dvd_prod {p : α} (hp : prime p) {s : multiset α} :
  (∀ r ∈ s, prime r) → p ∣ s.prod → ∃ q ∈ s, p ~ᵤ q :=
multiset.induction_on s (by simp [mt is_unit_iff_dvd_one.2 hp.2.1])
  (λ a s ih hs hps, begin
    rw [multiset.prod_cons] at hps,
    cases hp.2.2 _ _ hps with h h,
    { use [a, by simp],
      cases h with u hu,
      cases ((irreducible_of_prime (hs a (multiset.mem_cons.2
        (or.inl rfl)))).2 p u hu).resolve_left hp.2.1 with v hv,
      exact ⟨v, by simp [hu, hv]⟩ },
    { rcases ih (λ r hr, hs _ (multiset.mem_cons.2 (or.inr hr))) h with ⟨q, hq₁, hq₂⟩,
      exact ⟨q, multiset.mem_cons.2 (or.inr hq₁), hq₂⟩ }
  end)

lemma associated_mul_left_cancel {a b c d : α} (h : a * b ~ᵤ c * d) (h₁ : a ~ᵤ c)
  (ha : a ≠ 0) : b ~ᵤ d :=
let ⟨u, hu⟩ := h in let ⟨v, hv⟩ := associated.symm h₁ in
⟨u * (v : units α), (domain.mul_left_inj ha).1
  begin
    rw [← hv, mul_assoc c (v : α) d, mul_left_comm c, ← hu],
    simp [hv.symm, mul_assoc, mul_comm, mul_left_comm]
  end⟩

noncomputable instance : unique_factorization_domain α :=
{ factors := λ a, if ha : a = 0 then 0 else classical.some (factors_aux a ha),
  factors_prod := λ a ha, by rw dif_neg ha;
    exact associated.symm (classical.some_spec (factors_aux a ha)).1,
  irreducible_factors := λ a ha, by rw dif_neg ha;
    exact (classical.some_spec (factors_aux a ha)).2,
  unique := λ f, multiset.induction_on f
      (λ g _ hg h,
        multiset.rel_zero_left.2 $
          multiset.eq_zero_of_forall_not_mem (λ x hx,
            have is_unit g.prod, by simpa [associated_one_iff_is_unit] using h.symm,
            (hg x hx).1 (is_unit_iff_dvd_one.2 (dvd.trans (multiset.dvd_prod hx)
              (is_unit_iff_dvd_one.1 this)))))
      (λ p f ih g hf hg hfg,
        let ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod
          (prime_of_irreducible (hf p (by simp)))
          (λ q hq, prime_of_irreducible (hg _ hq)) $
            (dvd_iff_dvd_of_rel_right hfg).1
              (show p ∣ (p :: f).prod, by simp) in
        begin
          rw ← multiset.cons_erase hbg,
          exact multiset.rel.cons hb (ih (λ q hq, hf _ (by simp [hq]))
            (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))
            (associated_mul_left_cancel
              (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
            (nonzero_of_irreducible (hf p (by simp)))))
        end),
  ..I }

end hidden
#exit
/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Cast of characters:

`P`   : a polynomial functor
`W`   : its W-type
`M`   : its M-type
`F`   : a functor
`q`   : `qpf` data, representing `F` as a quotient of `P`

The main goal is to construct:

`fix`   : the initial algebra with structure map `F fix → fix`.
`cofix` : the final coalgebra with structure map `cofix → F cofix`

We also show that the composition of qpfs is a qpf, and that the quotient of a qpf
is a qpf.
-/
import tactic.interactive data.multiset
universe u

/-
Facts about the general quotient needed to construct final coalgebras.
-/




namespace quot

def factor {α : Type*} (r s: α → α → Prop) (h : ∀ x y, r x y → s x y) :
  quot r → quot s :=
quot.lift (quot.mk s) (λ x y rxy, quot.sound (h x y rxy))

def factor_mk_eq {α : Type*} (r s: α → α → Prop) (h : ∀ x y, r x y → s x y) :
  factor r s h ∘ quot.mk _= quot.mk _ := rfl

end quot

/-
A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P.apply α`.

An element of `P.apply α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/

structure pfunctor :=
(A : Type u) (B : A → Type u)

namespace pfunctor

variables (P : pfunctor) {α β : Type u}

-- TODO: generalize to psigma?
def apply (α : Type*) := Σ x : P.A, P.B x → α

def map {α β : Type*} (f : α → β) : P.apply α → P.apply β :=
λ ⟨a, g⟩, ⟨a, f ∘ g⟩

instance : functor P.apply := {map := @map P}

theorem map_eq {α β : Type*} (f : α → β) (a : P.A) (g : P.B a → α) :
  @functor.map P.apply _ _ _ f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
rfl

theorem id_map {α : Type*} : ∀ x : P.apply α, id <$> x = id x :=
λ ⟨a, b⟩, rfl

theorem comp_map {α β γ : Type*} (f : α → β) (g : β → γ) :
  ∀ x : P.apply α, (g ∘ f) <$> x = g <$> (f <$> x) :=
λ ⟨a, b⟩, rfl

instance : is_lawful_functor P.apply :=
{id_map := @id_map P, comp_map := @comp_map P}

inductive W
| mk (a : P.A) (f : P.B a → W) : W

def W_dest : W P → P.apply (W P)
| ⟨a, f⟩ := ⟨a, f⟩

def W_mk : P.apply (W P) → W P
| ⟨a, f⟩ := ⟨a, f⟩

@[simp] theorem W_dest_W_mk (p : P.apply (W P)) : P.W_dest (P.W_mk p) = p :=
by cases p; reflexivity

@[simp] theorem W_mk_W_dest (p : W P) : P.W_mk (P.W_dest p) = p :=
by cases p; reflexivity

end pfunctor

/-
Quotients of polynomial functors.

Roughly speaking, saying that `F` is a quotient of a polynomial functor means that for each `α`,
elements of `F α` are represented by pairs `⟨a, f⟩`, where `a` is the shape of the object and
`f` indexes the relevant elements of `α`, in a suitably natural manner.
-/

class qpf (F : Type u → Type u) [functor F] :=
(P         : pfunctor.{u})
(abs       : Π {α}, P.apply α → F α)
(repr      : Π {α}, F α → P.apply α)
(abs_repr  : ∀ {α} (x : F α), abs (repr x) = x)
(abs_map   : ∀ {α β} (f : α → β) (p : P.apply α), abs (f <$> p) = f <$> abs p)

namespace qpf
variables {F : Type u → Type u} [functor F] [q : qpf F]
include q

attribute [simp] abs_repr

/-
Show that every qpf is a lawful functor.

Note: every functor has a field, map_comp, and is_lawful_functor has the defining
characterization. We can only propagate the assumption.
-/

theorem id_map {α : Type*} (x : F α) : id <$> x = x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map], reflexivity }

theorem comp_map {α β γ : Type*} (f : α → β) (g : β → γ) (x : F α) :
  (g ∘ f) <$> x = g <$> f <$> x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map, ←abs_map, ←abs_map], reflexivity }

theorem is_lawful_functor
  (h : ∀ α β : Type u, @functor.map_const F _ α _ = functor.map ∘ function.const β) : is_lawful_functor F :=
{ map_const_eq := h,
  id_map := @id_map F _ _,
  comp_map := @comp_map F _ _ }

/-
Think of trees in the `W` type corresponding to `P` as representatives of elements of the
least fixed point of `F`, and assign a canonical representative to each equivalence class
of trees.
-/

/-- does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
def recF {α : Type*} (g : F α → α) : q.P.W → α
| ⟨a, f⟩ := g (abs ⟨a, λ x, recF (f x)⟩)

theorem recF_eq {α : Type*} (g : F α → α) (x : q.P.W) :
  recF g x = g (abs (recF g <$> q.P.W_dest x)) :=
by cases x; reflexivity

theorem recF_eq' {α : Type*} (g : F α → α) (a : q.P.A) (f : q.P.B a → q.P.W) :
  recF g ⟨a, f⟩ = g (abs (recF g <$> ⟨a, f⟩)) :=
rfl

/-- two trees are equivalent if their F-abstractions are -/
inductive Wequiv : q.P.W → q.P.W → Prop
| ind (a : q.P.A) (f f' : q.P.B a → q.P.W) :
    (∀ x, Wequiv (f x) (f' x)) → Wequiv ⟨a, f⟩ ⟨a, f'⟩
| abs (a : q.P.A) (f : q.P.B a → q.P.W) (a' : q.P.A) (f' : q.P.B a' → q.P.W) :
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → Wequiv ⟨a, f⟩ ⟨a', f'⟩
| trans (u v w : q.P.W) : Wequiv u v → Wequiv v w → Wequiv u w

/-- recF is insensitive to the representation -/
theorem recF_eq_of_Wequiv {α : Type u} (u : F α → α) (x y : q.P.W) :
  Wequiv x y → recF u x = recF u y :=
begin
  cases x with a f, cases y with b g,
  intro h, induction h,
  case qpf.Wequiv.ind : a f f' h ih
    { simp only [recF_eq', pfunctor.map_eq, function.comp, ih] },
  case qpf.Wequiv.abs : a f a' f' h ih
    { simp only [recF_eq', abs_map, h] },
  case qpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { exact eq.trans ih₁ ih₂ }
end

theorem Wequiv.abs' (x y : q.P.W) (h : abs (q.P.W_dest x) = abs (q.P.W_dest y)) :
  Wequiv x y :=
by { cases x, cases y, apply Wequiv.abs, apply h }

theorem Wequiv.refl (x : q.P.W) : Wequiv x x :=
by cases x with a f; exact Wequiv.abs a f a f rfl

theorem Wequiv.symm (x y : q.P.W) : Wequiv x y → Wequiv y x :=
begin
  cases x with a f, cases y with b g,
  intro h, induction h,
  case qpf.Wequiv.ind : a f f' h ih
    { exact Wequiv.ind _ _ _ ih },
  case qpf.Wequiv.abs : a f a' f' h ih
    { exact Wequiv.abs _ _ _ _ h.symm },
  case qpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { exact qpf.Wequiv.trans _ _ _ ih₂ ih₁}
end

/-- maps every element of the W type to a canonical representative -/
def Wrepr : q.P.W → q.P.W := recF (q.P.W_mk ∘ repr)

theorem Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x :=
begin
  induction x with a f ih,
  apply Wequiv.trans,
  { change Wequiv (Wrepr ⟨a, f⟩) (q.P.W_mk (Wrepr <$> ⟨a, f⟩)),
    apply Wequiv.abs',
    have : Wrepr ⟨a, f⟩ = q.P.W_mk (repr (abs (Wrepr <$> ⟨a, f⟩))) := rfl,
    rw [this, pfunctor.W_dest_W_mk, abs_repr],
    reflexivity },
  apply Wequiv.ind, exact ih
end

/-
Define the fixed point as the quotient of trees under the equivalence relation.
-/

def W_setoid : setoid q.P.W :=
⟨Wequiv, @Wequiv.refl _ _ _, @Wequiv.symm _ _ _, @Wequiv.trans _ _ _⟩

local attribute [instance] W_setoid

def fix (F : Type u → Type u) [functor F] [q : qpf F]:= quotient (W_setoid : setoid q.P.W)

def fix.rec {α : Type*} (g : F α → α) : fix F → α :=
quot.lift (recF g) (recF_eq_of_Wequiv g)

def fix_to_W : fix F → q.P.W :=
quotient.lift Wrepr (recF_eq_of_Wequiv (λ x, q.P.W_mk (repr x)))

def fix.mk (x : F (fix F)) : fix F := quot.mk _ (q.P.W_mk (fix_to_W <$> repr x))

def fix.dest : fix F → F (fix F) := fix.rec (functor.map fix.mk)

theorem fix.rec_eq {α : Type*} (g : F α → α) (x : F (fix F)) :
  fix.rec g (fix.mk x) = g (fix.rec g <$> x) :=
have recF g ∘ fix_to_W = fix.rec g,
  by { apply funext, apply quotient.ind, intro x, apply recF_eq_of_Wequiv,
       apply Wrepr_equiv },
begin
  conv { to_lhs, rw [fix.rec, fix.mk], dsimp },
  cases h : repr x with a f,
  rw [pfunctor.map_eq, recF_eq, ←pfunctor.map_eq, pfunctor.W_dest_W_mk, ←pfunctor.comp_map,
      abs_map, ←h, abs_repr, this]
end

theorem fix.ind_aux (a : q.P.A) (f : q.P.B a → q.P.W) :
  fix.mk (abs ⟨a, λ x, ⟦f x⟧⟩) = ⟦⟨a, f⟩⟧ :=
have fix.mk (abs ⟨a, λ x, ⟦f x⟧⟩) = ⟦Wrepr ⟨a, f⟩⟧,
  begin
    apply quot.sound, apply Wequiv.abs',
    rw [pfunctor.W_dest_W_mk, abs_map, abs_repr, ←abs_map, pfunctor.map_eq],
    conv { to_rhs, simp only [Wrepr, recF_eq, pfunctor.W_dest_W_mk, abs_repr] },
    reflexivity
  end,
by { rw this, apply quot.sound, apply Wrepr_equiv }

theorem fix.ind {α : Type*} (g₁ g₂ : fix F → α)
    (h : ∀ x : F (fix F), g₁ <$> x = g₂ <$> x → g₁ (fix.mk x) = g₂ (fix.mk x)) :
  ∀ x, g₁ x = g₂ x :=
begin
  apply quot.ind,
  intro x,
  induction x with a f ih,
  change g₁ ⟦⟨a, f⟩⟧ = g₂ ⟦⟨a, f⟩⟧,
  rw [←fix.ind_aux a f], apply h,
  rw [←abs_map, ←abs_map, pfunctor.map_eq, pfunctor.map_eq],
  dsimp [function.comp],
  congr, ext x, apply ih
end

theorem fix.rec_unique {α : Type*} (g : F α → α) (h : fix F → α)
    (hyp : ∀ x, h (fix.mk x) = g (h <$> x)) :
  fix.rec g = h :=
begin
  ext x,
  apply fix.ind,
  intros x hyp',
  rw [hyp, ←hyp', fix.rec_eq]
end

theorem fix.mk_dest (x : fix F) : fix.mk (fix.dest x) = x :=
begin
  change (fix.mk ∘ fix.dest) x = id x,
  apply fix.ind,
  intro x, dsimp,
  rw [fix.dest, fix.rec_eq, id_map, comp_map],
  intro h, rw h
end

theorem fix.dest_mk (x : F (fix F)) : fix.dest (fix.mk x) = x :=
begin
  unfold fix.dest, rw [fix.rec_eq, ←fix.dest, ←comp_map],
  conv { to_rhs, rw ←(id_map x) },
  congr, ext x, apply fix.mk_dest
end

end qpf

/- Axiomatize the M construction for now -/

-- TODO: needed only because we axiomatize M
noncomputable theory

namespace pfunctor

axiom M (P : pfunctor.{u}) : Type u

-- TODO: are the universe ascriptions correct?
variables {P : pfunctor.{u}} {α : Type u}

axiom M_dest : M P → P.apply (M P)

axiom M_corec : (α → P.apply α) → (α → M P)

axiom M_dest_corec (g : α → P.apply α) (x : α) :
  M_dest (M_corec g x) = M_corec g <$> g x

axiom M_bisim {α : Type*} (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      M_dest x = ⟨a, f⟩ ∧
      M_dest y = ⟨a, f'⟩ ∧
      ∀ i, R (f i) (f' i)) :
  ∀ x y, R x y → x = y

theorem M_bisim' {α : Type*} (Q : α → Prop) (u v : α → M P)
    (h : ∀ x, Q x → ∃ a f f',
      M_dest (u x) = ⟨a, f⟩ ∧
      M_dest (v x) = ⟨a, f'⟩ ∧
      ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
  ∀ x, Q x → u x = v x :=
λ x Qx,
let R := λ w z : M P, ∃ x', Q x' ∧ w = u x' ∧ z = v x' in
@M_bisim P (M P) R
  (λ x y ⟨x', Qx', xeq, yeq⟩,
    let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx' in
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
  _ _ ⟨x, Qx, rfl, rfl⟩

-- for the record, show M_bisim follows from M_bisim'
theorem M_bisim_equiv (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      M_dest x = ⟨a, f⟩ ∧
      M_dest y = ⟨a, f'⟩ ∧
      ∀ i, R (f i) (f' i)) :
  ∀ x y, R x y → x = y :=
λ x y Rxy,
let Q : M P × M P → Prop := λ p, R p.fst p.snd in
M_bisim' Q prod.fst prod.snd
  (λ p Qp,
    let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp in
    ⟨a, f, f', hx, hy, λ i, ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
  ⟨x, y⟩ Rxy

theorem M_corec_unique (g : α → P.apply α) (f : α → M P)
    (hyp : ∀ x, M_dest (f x) = f <$> (g x)) :
  f = M_corec g :=
begin
  ext x,
  apply M_bisim' (λ x, true) _ _ _ _ trivial,
  clear x,
  intros x _,
  cases gxeq : g x with a f',
  have h₀ : M_dest (f x) = ⟨a, f ∘ f'⟩,
  { rw [hyp, gxeq, pfunctor.map_eq] },
  have h₁ : M_dest (M_corec g x) = ⟨a, M_corec g ∘ f'⟩,
  { rw [M_dest_corec, gxeq, pfunctor.map_eq], },
  refine ⟨_, _, _, h₀, h₁, _⟩,
  intro i,
  exact ⟨f' i, trivial, rfl, rfl⟩
end

def M_mk : P.apply (M P) → M P := M_corec (λ x, M_dest <$> x)

theorem M_mk_M_dest (x : M P) : M_mk (M_dest x) = x :=
begin
  apply M_bisim' (λ x, true) (M_mk ∘ M_dest) _ _ _ trivial,
  clear x,
  intros x _,
  cases Mxeq : M_dest x with a f',
  have : M_dest (M_mk (M_dest x)) = ⟨a, _⟩,
  { rw [M_mk, M_dest_corec, Mxeq, pfunctor.map_eq, pfunctor.map_eq] },
  refine ⟨_, _, _, this, rfl, _⟩,
  intro i,
  exact ⟨f' i, trivial, rfl, rfl⟩
end

theorem M_dest_M_mk (x : P.apply (M P)) : M_dest (M_mk x) = x :=
begin
  have : M_mk ∘ M_dest = id := funext M_mk_M_dest,
  rw [M_mk, M_dest_corec, ←comp_map, ←M_mk, this, id_map, id]
end

end pfunctor

/-
Construct the final coalebra to a qpf.
-/

namespace qpf
variables {F : Type u → Type u} [functor F] [q : qpf F]
include q

/-- does recursion on `q.P.M` using `g : α → F α` rather than `g : α → P α` -/
def corecF {α : Type*} (g : α → F α) : α → q.P.M :=
pfunctor.M_corec (λ x, repr (g x))

theorem corecF_eq {α : Type*} (g : α → F α) (x : α) :
  pfunctor.M_dest (corecF g x) = corecF g <$> repr (g x) :=
by rw [corecF, pfunctor.M_dest_corec]

/- Equivalence -/

/- A pre-congruence on q.P.M *viewed as an F-coalgebra*. Not necessarily symmetric. -/
def is_precongr (r : q.P.M → q.P.M → Prop) : Prop :=
  ∀ ⦃x y⦄, r x y →
    abs (quot.mk r <$> pfunctor.M_dest x) = abs (quot.mk r <$> pfunctor.M_dest y)

/- The maximal congruence on q.P.M -/
def Mcongr : q.P.M → q.P.M → Prop :=
λ x y, ∃ r, is_precongr r ∧ r x y

def cofix (F : Type u → Type u) [functor F] [q : qpf F]:= quot (@Mcongr F _ q)

def cofix.corec {α : Type*} (g : α → F α) : α → cofix F :=
λ x, quot.mk  _ (corecF g x)

def cofix.dest : cofix F → F (cofix F) :=
quot.lift
  (λ x, quot.mk Mcongr <$> (abs (pfunctor.M_dest x)))
  begin
    rintros x y ⟨r, pr, rxy⟩, dsimp,
    have : ∀ x y, r x y → Mcongr x y,
    { intros x y h, exact ⟨r, pr, h⟩ },
    rw [←quot.factor_mk_eq _ _ this], dsimp,
    conv { to_lhs, rw [comp_map, ←abs_map, pr rxy, abs_map, ←comp_map] }
  end

theorem cofix.dest_corec {α : Type u} (g : α → F α) (x : α) :
  cofix.dest (cofix.corec g x) = cofix.corec g <$> g x :=
begin
  conv { to_lhs, rw [cofix.dest, cofix.corec] }, dsimp,
  rw [corecF_eq, abs_map, abs_repr, ←comp_map], reflexivity
end

private theorem cofix.bisim_aux
    (r : cofix F → cofix F → Prop)
    (h' : ∀ x, r x x)
    (h : ∀ x y, r x y → quot.mk r <$> cofix.dest x = quot.mk r <$> cofix.dest y) :
  ∀ x y, r x y → x = y :=
begin
  intro x, apply quot.induction_on x, clear x,
  intros x y, apply quot.induction_on y, clear y,
  intros y rxy,
  apply quot.sound,
  let r' := λ x y, r (quot.mk _ x) (quot.mk _ y),
  have : is_precongr r',
  { intros a b r'ab,
    have  h₀: quot.mk r <$> quot.mk Mcongr <$> abs (pfunctor.M_dest a) =
              quot.mk r <$> quot.mk Mcongr <$> abs (pfunctor.M_dest b) := h _ _ r'ab,
    have h₁ : ∀ u v : q.P.M, Mcongr u v → quot.mk r' u = quot.mk r' v,
    { intros u v cuv, apply quot.sound, dsimp [r'], rw quot.sound cuv, apply h' },
    let f : quot r → quot r' := quot.lift (quot.lift (quot.mk r') h₁)
      begin
        intro c, apply quot.induction_on c, clear c,
        intros c d, apply quot.induction_on d, clear d,
        intros d rcd, apply quot.sound, apply rcd
      end,
    have : f ∘ quot.mk r ∘ quot.mk Mcongr = quot.mk r' := rfl,
    rw [←this, pfunctor.comp_map _ _ f, pfunctor.comp_map _ _ (quot.mk r),
          abs_map, abs_map, abs_map, h₀],
    rw [pfunctor.comp_map _ _ f, pfunctor.comp_map _ _ (quot.mk r),
          abs_map, abs_map, abs_map] },
  refine ⟨r', this, rxy⟩
end

theorem cofix.bisim
    (r : cofix F → cofix F → Prop)
    (h : ∀ x y, r x y → quot.mk r <$> cofix.dest x = quot.mk r <$> cofix.dest y) :
  ∀ x y, r x y → x = y :=
let r' x y := x = y ∨ r x y in
begin
  intros x y rxy,
  apply cofix.bisim_aux r',
  { intro x, left, reflexivity },
  { intros x y r'xy,
    cases r'xy, { rw r'xy },
    have : ∀ x y, r x y → r' x y := λ x y h, or.inr h,
    rw ←quot.factor_mk_eq _ _ this, dsimp,
    rw [@comp_map _ _ q _ _ _ (quot.mk r), @comp_map _ _ q _ _ _ (quot.mk r)],
    rw h _ _ r'xy },
  right, exact rxy
end

/-
TODO:
- define other two versions of relation lifting (via subtypes, via P)
- derive other bisimulation principles.
- define mk and prove identities.
-/

end qpf

/-
Composition of qpfs.
-/

namespace pfunctor

/-
def comp : pfunctor.{u} → pfunctor.{u} → pfunctor.{u}
| ⟨A₂, B₂⟩ ⟨A₁, B₁⟩ := ⟨Σ a₂ : A₂, B₂ a₂ → A₁, λ ⟨a₂, a₁⟩, Σ u : B₂ a₂, B₁ (a₁ u)⟩
-/

def comp (P₂ P₁ : pfunctor.{u}) : pfunctor.{u} :=
⟨ Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1,
  λ a₂a₁, Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u) ⟩

end pfunctor

namespace qpf

variables {F₂ : Type u → Type u} [functor F₂] [q₂ : qpf F₂]
variables {F₁ : Type u → Type u} [functor F₁] [q₁ : qpf F₁]
include q₂ q₁

def comp : qpf (functor.comp F₂ F₁) :=
{ P := pfunctor.comp (q₂.P) (q₁.P),
  abs := λ α,
    begin
      dsimp [functor.comp],
      intro p,
      exact abs ⟨p.1.1, λ x, abs ⟨p.1.2 x, λ y, p.2 ⟨x, y⟩⟩⟩
    end,
  repr := λ α,
    begin
      dsimp [functor.comp],
      intro y,
      refine ⟨⟨(repr y).1, λ u, (repr ((repr y).2 u)).1⟩, _⟩,
      dsimp [pfunctor.comp],
      intro x,
      exact (repr ((repr y).2 x.1)).snd x.2
    end,
  abs_repr := λ α,
    begin
      abstract {
      dsimp [functor.comp],
      intro x,
      conv { to_rhs, rw ←abs_repr x},
      cases h : repr x with a f,
      dsimp,
      congr,
      ext x,
      cases h' : repr (f x) with b g,
      dsimp, rw [←h', abs_repr] }
    end,
  abs_map := λ α β f,
    begin
      abstract {
      dsimp [functor.comp, pfunctor.comp],
      intro p,
      cases p with a g, dsimp,
      cases a with b h, dsimp,
      symmetry,
      transitivity,
      symmetry,
      apply abs_map,
      congr,
      rw pfunctor.map_eq,
      dsimp [function.comp],
      simp [abs_map],
      split,
      reflexivity,
      ext x,
      rw ←abs_map,
      reflexivity }
    end
}

end qpf


/-
Quotients.

We show that if `F` is a qpf and `G` is a suitable quotient of `F`, then `G` is a qpf.
-/

namespace qpf
variables {F : Type u → Type u} [functor F] [q : qpf F]
variables {G : Type u → Type u} [functor G]
variable  {FG_abs  : Π {α}, F α → G α}
variable  {FG_repr : Π {α}, G α → F α}

def quotient_qpf
    (FG_abs_repr : Π {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map  : ∀ {α β} (f : α → β) (x : F α), FG_abs (f <$> x) = f <$> FG_abs x) :
  qpf G :=
{ P        := q.P,
  abs      := λ {α} p, FG_abs (abs p),
  repr     := λ {α} x, repr (FG_repr x),
  abs_repr := λ {α} x, by rw [abs_repr, FG_abs_repr],
  abs_map  := λ {α β} f x, by { rw [abs_map, FG_abs_map] } }

end qpf

#exit
import group_theory.subgroup group_theory.perm

universe u

open finset equiv equiv.perm

class simple_group {G : Type*} [group G] :=
(simple : ∀ (H : set G) [normal_subgroup H], H = set.univ ∨ H = is_subgroup.trivial G)

variables {G : Type*} [group G] [fintype G] [decidable_eq G]

def conjugacy_class (a : G) : finset G :=
(@univ G _).image (λ x, x * a * x⁻¹)

@[simp] lemma mem_conjugacy_class {a b : G} : b ∈ conjugacy_class a ↔ is_conj a b :=
by simp [conjugacy_class, mem_image, is_conj, eq_comm]

def subgroup_closure (s : finset G) : finset G :=
insert 1 ((s.product s).image (λ a, a.1 * a.2⁻¹))

instance subgroup_closure.is_subgroup (s : finset G) :
  is_subgroup (↑(subgroup_closure s) : set G) :=
{ one_mem := by simp [subgroup_closure],
  mul_mem := sorry,
  inv_mem := sorry }

def alternating (α : Type u) [fintype α] [decidable_eq α] : Type u :=
is_group_hom.ker (sign : perm α → units ℤ)

instance (α : Type u) [fintype α] [decidable_eq α] : group (alternating α) :=
by unfold alternating; apply_instance

instance (α : Type u) [fintype α] [decidable_eq α] :
  fintype (alternating α) :=
by simp [alternating, is_group_hom.ker];
exact subtype.fintype _

#eval conjugacy_class (show alternating (fin 5),
  from ⟨swap 1 2 * swap 2 3, by simp [is_group_hom.ker]; refl⟩)



#exit
def next_aux (N : nat) : list nat -> nat
| [] := 0
| (hd :: tl) := if hd < N then 0 else next_aux tl + 1

def next (m : nat) : list nat -> list nat
| [] := []
| (0 :: tl) := tl
| ((n+1) :: tl) := let index := next_aux (n+1) tl,
    B := n :: list.take index tl,
    G := list.drop index tl in
    ((++ B)^[m+1] B) ++ G

-- Beklemishev's worms
def worm_step (initial : nat) : Π step : nat, list nat
| 0 := [initial]
| (m+1) := next m (worm_step m)

#eval (list.range 10).map (worm_step 3)

-- It will terminate
theorem worm_principle : ∀ n, ∃ s, worm_step n s = []
| 0 := ⟨1, rfl⟩
| (n+1) := begin


end


-- def Fin : nat → Type
--   | 0 := empty
--   | (n+1) := option (Fin n)

inductive Fin : nat → Type
| mk {n : ℕ} : option (Fin n) → Fin (n + 1)


#exit

import analysis.topology.continuity

#print axioms continuous

local attribute [instance] classical.prop_decidable

import analysis.topology.continuity

lemma continuous_of_const {α : Type*} {β : Type*} [topological_space α]
  [topological_space β] {f : α → β} (h : ∀a b, f a = f b) : continuous f :=
λ s hs, _

#exit
example {α : Type*} (r : α → α → Prop)
  (h : ∀ f : ℕ → α, ∃ n, ¬r (f (n + 1)) (f n)) :
  well_founded r :=
let f : Π a : α, �� acc r a → {b : α // ¬ acc r b ∧ r b a} :=
  λ a ha, classical.indefinite_description _
    (classical.by_contradiction
      (λ hc, ha $ acc.intro _ (λ y hy,
        classical.by_contradiction (λ hy1, hc ⟨y, hy1, hy⟩)))) in
well_founded.intro
  (λ a, classical.by_contradiction
    (λ ha, let g : Π n : ℕ, {b : α // ¬ acc r b} := λ n, nat.rec_on n ⟨a, ha⟩
        (λ n b, ⟨f b.1 b.2, (f b.1 b.2).2.1⟩ ) in
      have hg : ∀ n, r (g (n + 1)) (g n),
        from λ n, nat.rec_on n (f _ _).2.2
          (λ n hn, (f _ _).2.2),
      exists.elim (h (subtype.val ∘ g)) (λ n hn, hn (hg _))))



example {α : Type*} (r : α → α → Prop)
  (h : well_founded r) (f : ℕ → α) :
  ∃ n, ¬r (f (n + 1)) (f n) :=
classical.by_contradiction (λ hr,
  @well_founded.fix α (λ a, ∀ n, a ≠ f n) r h
  (λ a ih n hn, ih (f (n + 1)) (classical.by_contradiction (hn.symm ▸ λ h, hr ⟨_, h⟩)) (n + 1) rfl)
  (f 0) 0 rfl )

lemma well_founded_iff_descending_chain {α : Type*} (r : α → α → Prop) :
  well_founded r ↔ ∀ f : ℕ → α, ∃ n, ¬ r (f (n + 1)) (f n) :=
⟨λ h f, classical.by_contradiction (λ hr,
    @well_founded.fix α (λ a, ∀ n, a ≠ f n) r h
      (λ a ih n hn, ih (f (n + 1))
        (classical.by_contradiction (hn.symm ▸ λ h, hr ⟨_, h⟩)) (n + 1) rfl)
      (f 0) 0 rfl),
  λ h, let f : Π a : α, ¬ acc r a → {b : α // ¬ acc r b ∧ r b a} :=
      λ a ha, classical.indefinite_description _
        (classical.by_contradiction
          (λ hc, ha $ acc.intro _ (λ y hy,
            classical.by_contradiction (λ hy1, hc ⟨y, hy1, hy⟩)))) in
    well_founded.intro
      (λ a, classical.by_contradiction
        (λ ha,
          let g : Π n : ℕ, {b : α // ¬ acc r b} :=
            λ n, nat.rec_on n ⟨a, ha⟩
              (λ n b, ���f b.1 b.2, (f b.1 b.2).2.1⟩) in
          have hg : ∀ n, r (g (n + 1)) (g n),
            from λ n, nat.rec_on n (f _ _).2.2
              (λ n hn, (f _ _).2.2),
          exists.elim (h (subtype.val ∘ g)) (λ n hn, hn (hg _))))⟩

#exit
import data.set.lattice order.order_iso data.quot

universes u v

noncomputable theory

axiom choice2_aux {α : Sort u} : { choice : α → α // ∀ (a b : α), choice a = choice b }

def choice2 : Π {α : Sort u}, α → α := λ _, choice2_aux.1

lemma choice2_spec : ∀ {α : Sort u} (a b : α), choice2 a = choice2 b := λ _, choice2_aux.2

axiom univalence : ∀ {α β : Sort u}, α ≃ β → α = β

lemma trunc.out2 {α : Sort u} (a : trunc α) : α := trunc.lift_on a choice2 choice2_spec

section diaconescu
variable p : Sort u
include p

private def U (x : Sort u) := trunc (psum (trunc x) p)
private def V (x : Sort u) := trunc (psum (x → false) p)

private lemma exU : trunc (Σ' x : Sort u, U p x) :=
  trunc.mk ⟨punit, trunc.mk (psum.inl (trunc.mk punit.star))⟩
private lemma exV : trunc (Σ' x : Sort u, V p x) :=
  trunc.mk ⟨pempty, trunc.mk (psum.inl (λ h, pempty.rec_on _ h))⟩

/- TODO(Leo): check why the code generator is not ignoring (some exU)
   when we mark u as def. -/
private def u : Sort u := psigma.fst (choice2 (trunc.out2 (exU p)))

private def v : Sort u := psigma.fst (choice2 (trunc.out2 (exV p)))

set_option type_context.unfold_lemmas true
private lemma u_def : U p (u p) := psigma.snd (choice2 (trunc.out2 (exU p)))
private lemma v_def : V p (v p) := psigma.snd (choice2 (trunc.out2 (exV p)))

private lemma not_uv_or_p : psum ((u p) ≠ (v p)) p :=
psum.cases_on (trunc.out2 (u_def p))
  (assume hut : trunc (u p),
    psum.cases_on (trunc.out2 (v_def p))
      (assume hvf : v p → false,
        psum.inl (λ h, hvf (eq.rec_on h (trunc.out2 hut))))
      psum.inr)
  psum.inr

private lemma p_implies_uv (hp : p) : u p = v p :=
have hpred : U p = V p, from
  funext (assume x : Sort u,
    univalence
      { to_fun := λ _, trunc.mk (psum.inr hp),
        inv_fun := λ _, trunc.mk (psum.inr hp),
        left_inv := λ x, show trunc.mk _ = _, from subsingleton.elim _ _,
        right_inv := λ x, show trunc.mk _ = _, from subsingleton.elim _ _ }),
show (choice2 (trunc.out2 (exU p))).fst = (choice2 (trunc.out2 (exV p))).fst,
  from @eq.drec_on _ (U p)
    (λ α (h : (U p) = α),
      (choice2 (trunc.out2 (exU p))).fst =
      (@choice2 (Σ' x : Sort u, α x) (trunc.out2
        (eq.rec_on (show V p = α, from hpred.symm.trans h) (exV p)))).fst)
    (V p) hpred (by congr)

#print axioms p_implies_uv

theorem em : psum p (p → false) :=
psum.rec_on (not_uv_or_p p)
  (assume hne : u p ≠ v p, psum.inr (λ hp, hne (p_implies_uv p hp)))
  psum.inl

end diaconescu

def old_choice {α : Sort u} : nonempty α → α :=
psum.rec_on (em α) (λ a _, a)
  (function.swap (((∘) ∘ (∘)) false.elim nonempty.elim))
#print axioms old_choice
open tactic declaration

#eval do d ← get_decl `old_choice,
  match d with
  | defn _ _ _ v _ _ := do e ← tactic.whnf v
      tactic.transparency.all tt, trace e, skip
  | _ := skip
  end

#exit
open set
section chain
parameters {α : Type u} (r : α → α → Prop)
local infix ` ≺ `:50  := r

/-- A chain is a subset `c` satisfying
  `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ c`. -/
def chain (c : set α) := pairwise_on c (λx y, x ≺ y ∨ y ≺ x)
parameters {r}

theorem chain.total_of_refl [is_refl α r]
  {c} (H : chain c) {x y} (hx : x ∈ c) (hy : y ∈ c) :
  x ≺ y ∨ y ≺ x :=
if e : x = y then or.inl (e ▸ refl _) else H _ hx _ hy e

theorem chain.directed [is_refl α r]
  {c} (H : chain c) {x y} (hx : x ∈ c) (hy : y ∈ c) :
  ∃ z, z ∈ c ∧ x ≺ z ∧ y ≺ z :=
match H.total_of_refl hx hy with
| or.inl h := ⟨y, hy, h, refl _⟩
| or.inr h := ⟨x, hx, refl _, h⟩
end

theorem chain.mono {c c'} : c' ⊆ c → chain c → chain c' :=
pairwise_on.mono

theorem chain.directed_on [is_refl α r] {c} (H : chain c) : directed_on (≺) c :=
λ x xc y yc, let ⟨z, hz, h⟩ := H.directed xc yc in ⟨z, hz, h⟩

theorem chain_insert {c : set α} {a : α} (hc : chain c) (ha : ∀b∈c, b ≠ a → a ≺ b ∨ b ≺ a) :
  chain (insert a c) :=
forall_insert_of_forall
  (assume x hx, forall_insert_of_forall (hc x hx) (assume hneq, (ha x hx hneq).symm))
  (forall_insert_of_forall (assume x hx hneq, ha x hx $ assume h', hneq h'.symm) (assume h, (h rfl).rec _))

def super_chain (c₁ c₂ : set α) := chain c₂ ∧ c₁ ⊂ c₂

def is_max_chain (c : set α) := chain c ∧ ¬ (∃c', super_chain c c')

def succ_chain (c : set α) : set α :=
psum.rec_on (em2 {c' : set α // chain c ∧ super_chain c c'}) subtype.val (λ _, c)

theorem succ_spec {c : set α} (h : {c' // chain c ∧ super_chain c c'}) :
  super_chain c (succ_chain c) :=
let ⟨c', hc'⟩ := h in
have chain c ∧ super_chain c (some h),
  from @some_spec _ (λc', chain c ∧ super_chain c c') _,
by simp [succ_chain, dif_pos, h, this.right]

theorem chain_succ {c : set α} (hc : chain c) : chain (succ_chain c) :=
if h : ∃c', chain c ∧ super_chain c c' then
  (succ_spec h).left
else
  by simp [succ_chain, dif_neg, h]; exact hc

theorem super_of_not_max {c : set α} (hc₁ : chain c) (hc₂ : ¬ is_max_chain c) :
  super_chain c (succ_chain c) :=
begin
  simp [is_max_chain, not_and_distrib, not_forall_not] at hc₂,
  cases hc₂.neg_resolve_left hc₁ with c' hc',
  exact succ_spec ⟨c', hc₁, hc'⟩
end

theorem succ_increasing {c : set α} : c ⊆ succ_chain c :=
if h : ∃c', chain c ∧ super_chain c c' then
  have super_chain c (succ_chain c), from succ_spec h,
  this.right.left
else by simp [succ_chain, dif_neg, h, subset.refl]

inductive chain_closure : set α → Prop
| succ : ∀{s}, chain_closure s → chain_closure (succ_chain s)
| union : ∀{s}, (∀a∈s, chain_closure a) → chain_closure (⋃₀ s)

theorem chain_closure_empty : chain_closure ∅ :=
have chain_closure (⋃₀ ∅),
  from chain_closure.union $ assume a h, h.rec _,
by simp at this; assumption

theorem chain_closure_closure : chain_closure (⋃₀ chain_closure) :=
chain_closure.union $ assume s hs, hs

variables {c c₁ c₂ c₃ : set α}

private lemma chain_closure_succ_total_aux (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂)
  (h : ∀{c₃}, chain_closure c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ succ_chain c₃ ⊆ c₂) :
  c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁ :=
begin
  induction hc₁,
  case _root_.zorn.chain_closure.succ : c₃ hc₃ ih {
    cases ih with ih ih,
    { have h := h hc₃ ih,
      cases h with h h,
      { exact or.inr (h ▸ subset.refl _) },
      { exact or.inl h } },
    { exact or.inr (subset.trans ih succ_increasing) } },
  case _root_.zorn.chain_closure.union : s hs ih {
    refine (classical.or_iff_not_imp_right.2 $ λ hn, sUnion_subset $ λ a ha, _),
    apply (ih a ha).resolve_right,
    apply mt (λ h, _) hn,
    exact subset.trans h (subset_sUnion_of_mem ha) }
end

private lemma chain_closure_succ_total (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂) (h : c₁ ⊆ c₂) :
  c₂ = c₁ ∨ succ_chain c₁ ⊆ c₂ :=
begin
  induction hc₂ generalizing c₁ hc₁ h,
  case _root_.zorn.chain_closure.succ : c₂ hc₂ ih {
    have h₁ : c₁ ⊆ c₂ ∨ @succ_chain α r c₂ ⊆ c₁ :=
      (chain_closure_succ_total_aux hc₁ hc₂ $ assume c₁, ih),
    cases h₁ with h₁ h₁,
    { have h₂ := ih hc₁ h₁,
      cases h₂ with h₂ h₂,
      { exact (or.inr $ h₂ ▸ subset.refl _) },
      { exact (or.inr $ subset.trans h₂ succ_increasing) } },
    { exact (or.inl $ subset.antisymm h₁ h) } },
  case _root_.zorn.chain_closure.union : s hs ih {
    apply or.imp_left (assume h', subset.antisymm h' h),
    apply classical.by_contradiction,
    simp [not_or_distrib, sUnion_subset_iff, classical.not_forall],
    intros c₃ hc₃ h₁ h₂,
    have h := chain_closure_succ_total_aux hc₁ (hs c₃ hc₃) (assume c₄, ih _ hc₃),
    cases h with h h,
    { have h' := ih c₃ hc₃ hc₁ h,
      cases h' with h' h',
      { exact (h₁ $ h' ▸ subset.refl _) },
      { exact (h₂ $ subset.trans h' $ subset_sUnion_of_mem hc₃) } },
    { exact (h₁ $ subset.trans succ_increasing h) } }
end

theorem chain_closure_total (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂) : c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
have c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁,
  from chain_closure_succ_total_aux hc₁ hc₂ $ assume c₃ hc₃, chain_closure_succ_total hc₃ hc₂,
or.imp_right (assume : succ_chain c₂ ⊆ c₁, subset.trans succ_increasing this) this

theorem chain_closure_succ_fixpoint (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂)
  (h_eq : succ_chain c₂ = c₂) : c₁ ⊆ c₂ :=
begin
  induction hc₁,
  case _root_.zorn.chain_closure.succ : c₁ hc₁ h {
    exact or.elim (chain_closure_succ_total hc₁ hc₂ h)
      (assume h, h ▸ h_eq.symm ▸ subset.refl c₂) id },
  case _root_.zorn.chain_closure.union : s hs ih {
    exact (sUnion_subset $ assume c₁ hc₁, ih c₁ hc₁) }
end

theorem chain_closure_succ_fixpoint_iff (hc : chain_closure c) :
  succ_chain c = c ↔ c = ⋃₀ chain_closure :=
⟨assume h, subset.antisymm
    (subset_sUnion_of_mem hc)
    (chain_closure_succ_fixpoint chain_closure_closure hc h),
  assume : c = ⋃₀{c : set α | chain_closure c},
  subset.antisymm
    (calc succ_chain c ⊆ ⋃₀{c : set α | chain_closure c} :
        subset_sUnion_of_mem $ chain_closure.succ hc
      ... = c : this.symm)
    succ_increasing⟩

theorem chain_chain_closure (hc : chain_closure c) : chain c :=
begin
  induction hc,
  case _root_.zorn.chain_closure.succ : c hc h {
    exact chain_succ h },
  case _root_.zorn.chain_closure.union : s hs h {
    have h : ∀c∈s, zorn.chain c := h,
    exact assume c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq,
      have t₁ ⊆ t₂ ∨ t₂ ⊆ t₁, from chain_closure_total (hs _ ht₁) (hs _ ht₂),
      or.elim this
        (assume : t₁ ⊆ t₂, h t₂ ht₂ c₁ (this hc₁) c₂ hc₂ hneq)
        (assume : t₂ ⊆ t₁, h t₁ ht₁ c₁ hc₁ c₂ (this hc₂) hneq) }
end

def max_chain := ⋃₀ chain_closure

/-- Hausdorff's maximality principle

There exists a maximal totally ordered subset of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
theorem max_chain_spec : is_max_chain max_chain :=
classical.by_contradiction $
assume : ¬ is_max_chain (⋃₀ chain_closure),
have super_chain (⋃₀ chain_closure) (succ_chain (⋃₀ chain_closure)),
  from super_of_not_max (chain_chain_closure chain_closure_closure) this,
let ⟨h₁, h₂, (h₃ : (⋃₀ chain_closure) ≠ succ_chain (⋃₀ chain_closure))⟩ := this in
have succ_chain (⋃₀ chain_closure) = (⋃₀ chain_closure),
  from (chain_closure_succ_fixpoint_iff chain_closure_closure).mpr rfl,
h₃ this.symm

/-- Zorn's lemma

If every chain has an upper bound, then there is a maximal element -/
theorem zorn (h : ∀c, chain c → ∃ub, ∀a∈c, a ≺ ub) (trans : ∀{a b c}, a ≺ b → b ≺ c → a ≺ c) :
  ∃m, ∀a, m ≺ a → a ≺ m :=
have ∃ub, ∀a∈max_chain, a ≺ ub,
  from h _ $ max_chain_spec.left,
let ⟨ub, (hub : ∀a∈max_chain, a ≺ ub)⟩ := this in
⟨ub, assume a ha,
  have chain (insert a max_chain),
    from chain_insert max_chain_spec.left $ assume b hb _, or.inr $ trans (hub b hb) ha,
  have a ∈ max_chain, from
    classical.by_contradiction $ assume h : a ∉ max_chain,
    max_chain_spec.right $ ⟨insert a max_chain, this, ssubset_insert h⟩,
  hub a this⟩
end

#exit
import analysis.exponential group_theory.quotient_group

axiom R_iso_C : {f : ℝ ≃ ℂ // is_add_group_hom f}

open quotient_group

def R_mod_Z_iso_units_C : quotient_add_group.quotient (gmultiples (1 : ℝ))
  ≃ units ℂ :=
calc units ℂ ≃

#exit
import data.real.basic tactic.norm_num
#print expr
--set_option pp.all true
lemma crazy (k l : ℕ) (h : l ≤ k): ((2:real)⁻¹)^k ≤ (2⁻¹)^l :=
begin
  apply pow_le_pow_of_le_one _ _ h,
  norm_num,
  norm_num1, norm_num1, simp,
  show (2 : ℝ)⁻¹ ≤ 1,
  norm_num1,

end

example {α : Type*} (h : α ≃ unit → false) {x : α} : α

import tactic.norm_num

set_option profiler true

lemma facebook_puzzle :
  let a := 154476802108746166441951315019919837485664325669565431700026634898253202035277999 in
  let b := 36875131794129999827197811565225474825492979968971970996283137471637224634055579 in
  let c := 4373612677928697257861252602371390152816537558161613618621437993378423467772036 in
  (a : ℚ) / (b + c) + b / (a + c) + c / (a + b) = 4 := by norm_num

#print facebook_puzzle
#print axioms facebook_puzzle

#exit
import data.complex.basic

lemma

import data.quot

section

variables {α : Sort*} {β : α → Sort*} {γ : Sort*} [s : ∀ a : α, setoid (β a)]
include s

instance pi.setoid : setoid (Π a : α, β a) :=
{ r := λ x y, ∀ a : α, x a ≈ y a,
  iseqv := ⟨λ x a, setoid.refl _,
    λ x y h a, setoid.symm (h a),
    λ x y z hxy hyz a, setoid.trans (hxy a) (hyz a)⟩ }

meta def setoid_to_setoid (x : Π a : α, quotient (s a)) :
  quotient (@pi.setoid α β _) :=
quotient.mk (λ a, quot.unquot (x a))

axiom quotient.lift_onₙ (x : Π a : α, quotient (s a))
  (f : (Π a : α, β a) → γ) (h : ∀ x₁ x₂ : Π a, β a,
  (∀ a, x₁ a ≈ x₂ a) → f x₁ = f x₂) : γ
end

#print classical.axiom_of_choice

lemma choice {α : Sort*} {β : α → Sort*} {r : Π (x : α), β x → Prop}
  (h : ∀ (x : α), ∃ (y : β x), r x y) :
    ∃ (f : Π (x : α), β x), ∀ (x : α), r x (f x) :=
begin

end
lemma quotient.lift_on

#exit
import tactic.ring data.complex.basic

lemma h (x : ℝ) : x / 3 + x / -2 = x / 6 := by ring
set_option pp.all true
#print h

example (x : ℂ) : x / 3 + x / 2 = 5 * x / 6 := by ring

#exit
import tactic.interactive


-- private meta def collect_proofs_in :
--   expr → list expr → list name × list expr → tactic (list name × list expr)
-- | e ctx (ns, hs) :=
-- let go (tac : list name × list expr → tactic (list name × list expr)) :
--   tactic (list name × list expr) :=
-- (do t ← infer_type e,
--    mcond (is_prop t) (do
--      first (hs.map $ λ h, do
--        t' ← infer_type h,
--        is_def_eq t t',
--        g ← target,
--        change $ g.replace (λ a n, if a = e then some h else none),
--        return (ns, hs)) <|>
--      (let (n, ns) := (match ns with
--         | [] := (`_x, [])
--         | (n :: ns) := (n, ns)
--         end : name × list name) in
--       do generalize e n,
--          h ← intro n,
--          return (ns, h::hs)) <|> return (ns, hs)) (tac (ns, hs))) <|> return ([], []) in
-- match e with
-- | (expr.const _ _)   := go return
-- | (expr.local_const _ _ _ t) := collect_proofs_in t ctx (ns, hs)
-- | (expr.mvar _ _ t)  := collect_proofs_in t ctx (ns, hs)
-- | (expr.app f x)     :=
--   go (λ nh, collect_proofs_in f ctx nh >>= collect_proofs_in x ctx)
-- | (expr.lam n b d e) :=
--   go (λ nh, do
--     nh ← collect_proofs_in d ctx nh,
--     var ← mk_local' n b d,
--     collect_proofs_in (expr.instantiate_var e var) (var::ctx) nh)
-- | (expr.pi n b d e) := do
--   nh ← collect_proofs_in d ctx (ns, hs),
--   var ← mk_local' n b d,
--   collect_proofs_in (expr.instantiate_var e var) (var::ctx) nh
-- | (expr.elet n t d e) :=
--   go (λ nh, do
--     nh ← collect_proofs_in t ctx nh,
--     nh ← collect_proofs_in d ctx nh,
--     collect_proofs_in (expr.instantiate_var e d) ctx nh)
-- | (expr.macro m l) :=
--   go (λ nh, mfoldl (λ x e, collect_proofs_in e ctx x) nh l)
-- | _                  := return (ns, hs)
-- end

example {α : Type*} [ring α] (f : Π a : α, a ≠ 0 → α) (a b : α) (hb : b ≠ a) :
  f (b - a) (mt sub_eq_zero_iff_eq.1 hb) = 0 :=
begin
  generalize_proofs,

end

example {α : Type*} [ring α] (f : Π a : α, a ≠ 0 → α) (b : α ) (hb : b ≠ 0) :
  f b hb = 0 :=
begin
  generalize_proofs,

end

#exit
import data.set.basic data.set.lattice
import data.equiv.basic

structure partition (α : Type) :=
(C : set (set α))
(non_empty : ∀ c ∈ C, ∃ a : α, a ∈ c)
(disjoint : ∀ c d ∈ C, (∃ x, x ∈ c ∩ d) → c = d)
(all : ⋃₀ C = set.univ)

variable {α : Type}

definition partitions_equiv_relns :
{r : α → α → Prop | equivalence r} ≃ partition α :=
{ to_fun := λ r, ⟨⋃ a : α, {{b : α | r.1 a b}},
    λ c ⟨s, ⟨a, ha⟩, m⟩, ⟨a,
      by simp only [ha.symm, set.mem_singleton_iff] at m;
        rw m; exact r.2.1 a⟩,
    λ u v ⟨s, ⟨a, ha⟩, m⟩ ⟨t, ⟨b, hb⟩, n⟩ ⟨c, hc⟩, begin
      clear _fun_match _x _fun_match _x _fun_match _x,
      simp [hb.symm, ha.symm] at *,
      simp [m, n] at *,
      have := r.2.2.2 hc.1 (r.2.2.1 hc.2),
      exact set.ext (λ x, ⟨r.2.2.2 (r.2.2.1 this), r.2.2.2 this⟩),
    end,
    set.eq_univ_of_forall $ λ a, ⟨{b : α | r.val a b}, set.mem_Union.2 ⟨a, by simp⟩, r.2.1 a⟩⟩,
  inv_fun := λ p, ⟨λ a b, ∃ s ∈ p.1, a ∈ s ∧ b ∈ s,
    ⟨λ a, let ⟨s, hs⟩ := set.eq_univ_iff_forall.1 p.4 a in
      ⟨s, by tauto⟩,
    λ a b, by simp only [and.comm, imp_self],
    λ a b c ⟨s, hs₁, hs₂⟩ ⟨t, ht₁, ht₂⟩,
      ⟨s, hs₁, hs₂.1, have t = s, from p.3 _ _ ht₁ hs₁ ⟨b, ht₂.1, hs₂.2⟩, this ▸ ht₂.2⟩⟩⟩,
  left_inv := λ ⟨r, hr⟩, subtype.eq begin
        ext x y,
        exact ⟨λ ⟨s, ⟨a, ⟨b, hb⟩, m⟩, t, ht⟩, begin simp [hb.symm] at *, simp [m] at *,
          exact hr.2.2 (hr.2.1 t) ht, end,
      λ h, ⟨{b : α | r x b}, set.mem_Union.2 ⟨x, by simp⟩,
        by simp [*, hr.1 x] at *⟩⟩
    end,
  right_inv := λ ⟨C, hc₁, hc₂, hc₃⟩, partition.mk.inj_eq.mpr $
    set.ext $ λ s, begin

    end }


#exit
import analysis.topology.topological_space

open filter

variables {α : Type*} [topological_space α]

def X : filter α := generate {s | compact (-s)}

lemma tendsto_X_right {α β : Type*} [topological_space β] (f : filter α) (m : α → β) :
  tendsto m f X ↔ ∀ s, compact (-s) → m ⁻¹' s ∈ f.sets :=
by simp [X, tendsto, sets_iff_generate, map, set.subset_def]

lemma mem_generate_iff {s : set (set α)} (hs : ∀ u v, u ∈ s → v ∈ s → u ∩ v ∈ s) {t : set α} :
  t ∈ (generate s).sets ↔ ∃ u ∈ s, s ⊆ u :=
begin


end

lemma tendsto_X_left {α β : Type*} [topological_space α]
  [topological_space β] (m : α → β) : tendsto m X X :=
begin
  rw [tendsto_X_right, X],

end

#exit

instance : preorder ℂ :=
{ le := λ x y, x.abs ≤ y.abs,
  le_refl := λ x, le_refl x.abs,
  le_trans := λ x y z, @le_trans ℝ _ _ _ _ }
#print filter
example (f : ℂ → ℂ) : tendsto f at_top at_top ↔
  ∀ x : ℝ, ∃ r, ∀ z : ℂ, r < z.abs → x < (f z).abs

#exit
import data.zmod.basic

def dihedral (n : ℕ+) := units ℤ × zmod n

variable (n : ℕ+)

def mul : Π (x y : dihedral n), dihedral n
| ⟨ff, x⟩ ⟨ff, y⟩ :=


#exit
import tactic.interactive -- to get simpa

namespace random

open nat
set_option trace.simplify.rewrite true
@[semireducible] theorem add_right_cancel (n m k : nat) : n + k = m + k → n = m :=
begin
  induction k with k ih,
  { -- base case
    exact id, -- n = n + 0 is true by definition
  },
  { -- inductive step
    show succ (n + k) = succ (m + k) → _, -- again true by definition
    intro H,
    apply ih,
    injection H,
  }
end
#print axioms add_right_cancel

end random

#exit
universe u

@[derive decidable_eq] inductive poly_aux : Type
| zero : poly_aux
| X : poly_aux
| C : poly_aux

inductive polynomial_aux {α : Type u} [comm_semiring α] : poly_aux → Type u
| zero : polynomial_aux poly_aux.zero
| X : polynomial_aux poly_aux.X ⊕ polynomial_aux poly_aux.C → polynomial_aux poly_aux.X
| C {a : α} (h : a ≠ 0) : polynomial_aux poly_aux.zero ⊕ polynomial_aux poly_aux.X →
  polynomial_aux poly_aux.C

#exit
import analysis.metric_space

open set

set_option trace.simplify.rewrite true

lemma closed_ball_Icc {x r : ℝ} : closed_ball x r = Icc (x-r) (x+r) :=
by simp only [closed_ball, Icc, dist, abs_sub_le_iff,
  sub_le_iff_le_add', and.comm, add_comm]

#print closed_ball_Icc

#exit
import ring_theory.determinant data.polynomial
open polynomial
def M : matrix (fin 3) (fin 3) (polynomial ℤ) :=
λ r c, if r = 0 then if c = 1 then 1 else -1
  else if c = 0 then 0
  else if c = 1 then if r = 1 then -4 else -3
  else if r = 2 then 5 else 6

#exit
import algebra.archimedean
import data.real.basic

definition completeness_axiom (k : Type*) [preorder k] : Prop :=
∀ (S : set k), (∃ x, x ∈ S) → (∃ x, ∀ y ∈ S, y ≤ x) →
  ∃ x, ∀ y, x ≤ y ↔ ∀ z ∈ S, z ≤ y

lemma reals_complete : completeness_axiom ℝ :=
λ S hS₁ hS₂, ⟨real.Sup S, λ y, ⟨λ h z hz, le_trans (real.le_Sup S hS₂ hz) h,
  λ h, (real.Sup_le _ hS₁ hS₂).2 h⟩⟩

open function
section

parameters {K : Type*} {L : Type*} [discrete_linear_ordered_field K] [archimedean K]
  [discrete_linear_ordered_field L] [archimedean L] (hL : completeness_axiom L)

lemma f_exists (k : K) :
  ∃ x, ∀ y, x ≤ y ↔ ∀ z ∈ (rat.cast '' {q : ℚ | (q : K) ≤ k} : set L), z ≤ y :=
(hL (rat.cast '' {q : ℚ | (q : K) ≤ k})
  (let ⟨q, hq⟩ := exists_rat_lt k in ⟨q, ⟨q, ⟨le_of_lt hq, rfl⟩⟩⟩)
  (let ⟨q, hq⟩ := exists_rat_gt k in ⟨q, λ y ⟨g, hg⟩, hg.2 ▸ rat.cast_le.2 $
    (@rat.cast_le K _ _ _).1 (le_trans hg.1 (le_of_lt hq))⟩))

noncomputable def f (k : K) : L :=
classical.some (f_exists k)

lemma f_le_iff {q : ℚ} {k : K} : f k ≤ q ↔ k ≤ q :=
have ∀ (y : L), f k ≤ y ↔ ∀ (z : L), z ∈ rat.cast '' {q : ℚ | ↑q ≤ k} → z ≤ y,
    from classical.some_spec (f_exists k),
by rw this q; exact
  ⟨λ h, le_of_not_gt (λ h1, let ⟨r, hr⟩ := exists_rat_btwn h1 in
      not_le_of_gt hr.1 (rat.cast_le.2 (rat.cast_le.1 (h _ ⟨r, ⟨le_of_lt hr.2, rfl⟩⟩)))),
    λ h z ⟨g, hg⟩, hg.2 ▸ rat.cast_le.2 (rat.cast_le.1 (le_trans hg.1 h))⟩

lemma lt_f_iff {q : ℚ} {k : K} : (q : L) < f k ↔ (q : K) < k :=
by rw [← not_le, ← not_le, f_le_iff]

lemma le_f_iff {q : ℚ} {k : K} : (q : L) ≤ f k ↔ (q : K) ≤ k :=
⟨λ h, le_of_not_gt $ λ hk,
  let ⟨r, hr⟩ := exists_rat_btwn hk in
  not_lt_of_ge (f_le_iff.2 (le_of_lt hk))
    (lt_of_le_of_ne h (λ hq,
      by rw [rat.cast_lt, ← @rat.cast_lt L, hq, lt_f_iff] at hr;
        exact not_lt_of_gt hr.1 hr.2)),
  λ h, le_of_not_gt $ λ hk,
    let ⟨r, hr⟩ := exists_rat_btwn hk in
    not_lt_of_ge h $ lt_of_le_of_lt (f_le_iff.1 (le_of_lt hr.1))
        (rat.cast_lt.2 (rat.cast_lt.1 hr.2))⟩

lemma f_lt_iff {q : ℚ} {k : K} : f k < q ↔ k < q :=
by rw [← not_le, ← not_le, le_f_iff]

@[simp] lemma f_rat_cast (q : ℚ) : f q = q :=
le_antisymm (by rw f_le_iff) (by rw le_f_iff)

lemma f_injective : function.injective f :=
λ x y hxy, match lt_trichotomy x y with
| (or.inl h) := let ⟨q, hq⟩ := exists_rat_btwn h in
  by rw [← lt_f_iff, ← f_lt_iff] at hq;
    exact absurd hxy (ne_of_lt (lt_trans hq.1 hq.2))
| (or.inr (or.inl h)) := h
| (or.inr (or.inr h)) := let ⟨q, hq⟩ := exists_rat_btwn h in
  by rw [← lt_f_iff, ← f_lt_iff] at hq;
    exact absurd hxy.symm (ne_of_lt (lt_trans hq.1 hq.2))
end

lemma f_is_ring_hom : is_ring_hom f :=
⟨by rw [← rat.cast_one, f_rat_cast, rat.cast_one],
  λ x y, le_antisymm _ _,
  λ x y, le_antisymm
    (f_le_iff.2 _)
    _⟩

theorem characterisation_of_reals :
  ∃ f : K → ℝ, is_ring_hom f ∧ bijective f ∧ ∀ x y : K, x < y → f x < f y :=

end
#exit
import data.fintype

theorem Q0505 :
  ¬ (∃ a b c : ℕ, 6 * a + 9 * b + 20 * c = 43)
  ∧ ∀ m, m > 43 → ∃ a b c : ℕ, 6 * a + 9 * b + 20 * c = m :=


#exit
import data.nat.choose

open finset nat

theorem Q0403 : ∀ n : ℕ, finset.sum (finset.range n.succ)
  (λ i, (-1 : ℤ) ^ i * choose (2 * n) (2 * i)) = -2 ^ n
| 0 := rfl
| (n+1) := begin
  rw [sum_range_succ', function.comp],
  conv in (choose (2 * (n + 1)) (2 * succ _))
  { rw [mul_add, mul_succ, mul_zero, zero_add, mul_succ,
    choose_succ_succ, choose_succ_succ, choose_succ_succ],  },
  simp [sum_add_distrib, mul_add, *, -range_succ]
end

theorem Q0403 : finset.sum (finset.range 51)
  (λ i, (-1 : ℤ) ^ i * choose 100 (2 * i)) = 0 := sorry



def Fin : nat → Type
  | 0 := empty
  | (n+1) := option (Fin n)

inductive tm  : nat -> Type
  | var_tm : Π {ntm : nat}, Fin ntm -> tm ntm
  | app : Π {ntm : nat}, tm ntm -> tm ntm -> tm ntm
  | lam : Π {ntm : nat}, tm (nat.succ ntm) -> tm ntm

open tm

inductive type : Type
| tint : type
| tarrow : type → type → type

definition empty_ctx : Fin 0 → type.

local infix `⤏`:20 := type.tarrow

inductive types : Π{m : ℕ}, (Fin m → type) → tm m → type → Prop
| tvar {m} Γ (x : Fin m) : types Γ (var_tm x) (Γ x)
| tapp {m} Γ (e₁ : tm m) e₂ (A B) : types Γ e₁ (A ⤏ B) → types Γ e₂ A → types Γ (app e₁ e₂) B
-- | tlam {m} Γ (e : tm (nat.succ m)) (A B) : types (@scons _ m  A Γ) e B → types Γ (lam e) (A ⤏ B) requires some more definitions
def step {n} (t t' : tm n) := tt. --(..)
#print types.drec_on

lemma preservation (A : type) {n} (ctx : Fin n → type) (e₁ : tm 0) :
  types empty_ctx e₁ A →
      forall e₂, step e₁ e₂ → types empty_ctx e₂ A :=
λ H₁ e H₂,
begin
  destruct H₁, dsimp,
  exact sorry, exact sorry,

end


#print preservation
set_option trace.check true
lemma preservation (A : type) {n} (ctx : Fin n → type) (e₁ : tm 0) :
  types empty_ctx e₁ A →
      forall e₂, step e₁ e₂ → types empty_ctx e₂ A :=
λ H₁, @types.rec_on
  (λ m ctx e₁ t, m = 0 → ctx == empty_ctx → ∀ e₂ : tm m, step e₁ e₂ → types ctx e₂ A) 0 empty_ctx e₁ A H₁
    begin
      intros m Γ _ hm hΓ,
      subst hm,
      have := eq_of_heq hΓ,
      subst this,

    end sorry rfl (heq.refl _)

set_option trace.check true

lemma preservation1 (A : type) {n} (ctx : Fin n → type) (e₁ : tm 0) :
  types empty_ctx e₁ A →
      forall e₂, step e₁ e₂ → types empty_ctx e₂ A :=
begin
  intros H₁,
  induction H₁,


end

#print empty_ctx
def f : ℕ+ → ℕ+
| ⟨1, h⟩  :=

example (x y : ℕ ): (x + y) * 2 = sorry :=
begin
  simp [mul_comm],


end

example : real.partial_order = (@semilattice_inf.to_partial_order ℝ
       (@lattice.to_semilattice_inf ℝ
          (@conditionally_complete_lattice.to_lattice ℝ
             (@conditionally_complete_linear_order.to_conditionally_complete_lattice ℝ
                real.lattice.conditionally_complete_linear_order)))) := rfl

#print orderable_topology
#eval let n := 3 in let r := 2 in
  (fintype.card {f : fin r → fin n // function.injective f},
    fintype.card {f : fin n → fin r // function.surjective f})

#eval 93 / 3

#eval 2 ^ 5 - 2 * (1 ^ 5)

#eval 3 ^ 5 - 3 * (2 ^ 5 - (1 ^ 5))

#eval

#eval choose 5 2

#exit
import data.set.basic

class has_heart (α : Type*) := (heart : α → α → Prop)

notation a ` ♥ ` b := has_heart.heart a b

variables {α : Type*} [has_heart α]
def upper_bounds (s : set α) : set α := { x | ∀a ∈ s, a ♥ x }
def lower_bounds (s : set α) : set α := { x | ∀a ∈ s, x ♥ a }
def is_least (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ lower_bounds s
def is_greatest (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ upper_bounds s
def is_lub (s : set α) : α → Prop := is_least (upper_bounds s)
def is_glb (s : set α) : α → Prop := is_greatest (lower_bounds s)

theorem warm_up (S : Type) [has_heart S] :
  (∀ E : set S, (∃ a, a ∈ E) ∧ (∃ b, b ∈ upper_bounds E) → ∃ s : S, is_lub E s) →
  (∀ E : set S, (∃ a, a ∈ E) ∧ (∃ b, b ∈ lower_bounds E) → ∃ s : S, is_glb E s) :=
λ h E ⟨⟨e, he⟩, ⟨b, hb⟩⟩, let ⟨s, hs⟩ := h (lower_bounds E) ⟨⟨b, hb⟩, ⟨e, λ a ha, ha e he⟩⟩ in
  ⟨s, ⟨λ a ha, hs.2 _ (λ c hc, hc _ ha), hs.1⟩⟩

#print warm_up

#exit
import data.real.basic

structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

protected definition add : ℂ → ℂ → ℂ
| ⟨a, b⟩ ⟨c, d⟩ := ⟨a + c, b + d⟩
#print tactic.simp_config
notation a `+` b := complex.add a b
set_option trace.simplify.rewrite true
protected lemma add_assoc' (z1 z2 z3 : ℂ) : z1 + z2 + z3 = z1 + (z2 + z3) :=
begin
  cases z1 with x1 y1, cases z2 with x2 y2, cases z3 with x3 y3,
  simp only [complex.add, add_assoc],
  exact ⟨rfl, rfl⟩
end

#print complex.add_assoc'

end complex


#exit
import data.fintype group_theory.order_of_element algebra.pi_instances

variables {α : Type*} [fintype α] [decidable_eq α]

instance [group α] : decidable (∃ a : α, ∀ b : α, b ∈ gpowers a) :=
@fintype.decidable_exists_fintype α _ (λ a, ∀ b, b ∈ gpowers a)
  (λ a, @fintype.decidable_forall_fintype α _ (λ b, b ∈ gpowers a)
    (decidable_gpowers))

instance [group α] : decidable (is_cyclic α) :=



#exit
import data.rat.basic

inductive real : bool → Type
| of_rat : ℚ → real tt
| limit (x : Π q : ℚ, 0 < q → real tt) (∀ δ ε : ℚ, 0 < δ → 0 < ε → real ff ) :

mutual inductive A, B
with A : Type
| mk : B → A
with B : Type
| mk : A → B



def A.to_sort (l : Sort*) : A → l
| (A.mk (B.mk x)) := A.to_sort x

#print A.rec

def AB.reca : Π {Ca : A → Sort*}
  (ha : Π a : A, Ca a → Cb (B.mk a))
  (a : A), Ca a := λ _ _ _ _ a, A.to_sort _ a

def A.to_false (a : A) : false :=
AB.reca _ _ _

#print A.to_sort._main._pack
#exit
import data.finset analysis.metric_space

#print tactic.interactive.dsimp


example {α : Type*} (s : finset α) : s.card = 1 → {a : α // s = finset.singleton a} :=
finset.rec_on s (λ s, @quotient.rec_on_subsingleton _ _
  (λ t : multiset α, Π (nodup : multiset.nodup t),
    finset.card {val := t, nodup := nodup} = 1 → {a // finset.mk t nodup = finset.singleton a})
      (λ l, ⟨λ a b, funext (λ x, funext (λ y, subtype.eq $ finset.singleton_inj.1 $
        by rw [← (a x y).2, ← (b x y).2]))⟩) s
  (λ l, list.rec_on l (λ _ h, nat.no_confusion h)
    (λ a l _ _ h, have l.length = 0, from nat.succ_inj h,
      ⟨a, finset.eq_of_veq $ by dsimp; rw [list.length_eq_zero.1 this]; refl⟩)) )

#eval g ({1} : finset ℕ) rfl
#print metric_space
mutual inductive A, B
with A : Type
| mk : B → A
with B : Type
| mk : A → B

def size : A ⊕ B → ℕ
|

inductive AB : bool → Type
| mk_0 : AB ff → AB tt
| mk_1 : AB tt → AB ff

example (b : bool) (x : AB b) : false :=
AB.rec_on x (λ _, id) (λ _, id)

lemma A_mut_false(x : psum unit unit) (a : A._mut_ x) : false :=
  A._mut_.rec_on a (λ _, id) (λ _, id)

lemma h : A ⊕ B → false
| (sum.inl (A.mk b)) := h (sum.inr b)
| (sum.inr (B.mk a)) := h (sum.inl a)


example : A → false := h ∘ sum.inl

example : B → false := h ∘ sum.inr

#print prefix A
#print B
#print A._mut_

#exit
import analysis.exponential
#print quot.rec_on
universes u v
variable {α : Sort u}
variable {r : α → α → Prop}
variable {β : quot r → Sort v}
open quot
local notation `⟦`:max a `⟧` := quot.mk r a
attribute [simp] mul_comm


inductive Id {α : Type} (a : α) : α → Type
| refl : Id a

inductive Id2 {α : Type} : α → α → Type
| refl : Π a : α, Id2 a a

inductive eq2 {α : Type} : α → α → Prop
| refl : ∀ a : α, eq2 a a

lemma eq2_iff_eq {α : Type} (a b : α) : eq2 a b ↔ a = b :=
⟨λ h, eq2.rec (λ _, rfl) h, λ h, eq.rec (eq2.refl _) h⟩
universe l
example : Π {α : Type} {a b : α} {C : Id a b → Sort l},
  C (Id.refl a) → Π {a_1 : α} (n : Id a a_1), C a_1 n

#print Id.rec
#print eq.rec
#print Id2.rec
#print eq2.rec

local attribute [instance] classical.prop_decidable

example (α β : Type*) : ((α → β) → α) → α :=
if h : nonempty α then λ _, classical.choice h
else (λ f, f (λ a, (h ⟨a⟩).elim))


noncomputable example (α : Type*) : α ⊕ (α → empty) :=
if h : nonempty α then sum.inl (classical.choice h)
else sum.inr (λ a, (h ⟨a⟩).elim)

#print quot.ind
#print quot.rec
#print quot.lift
example : ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
  (∀ (a : α), β (mk r a)) → ∀ (q : quot r), β q :=
λ α r β f q, quot.rec f (λ _ _ _, rfl) q
set_option pp.proofs true
example : Π {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β),
  (∀ (a b : α), r a b → f a = f b) → quot r → β := λ α r β f h q,
  @quot.rec α r (λ _, β) f
  (λ a b hab, eq_of_heq (eq_rec_heq _ begin  end))

protected lemma lift_indep_pr1
  (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
  (q : quot r) : (lift (quot.indep f) (quot.indep_coherent f h) q).1 = q :=
quot.ind (by)

#exit
import analysis.topology.continuity data.zmod.basic
universe u
class t2_space1 (α : Type u) [topological_space α] : Prop :=
(t2 : ∀x y, x ≠ y → ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅)

class t2_space2 (α : Type u) [topological_space α] : Prop :=
(t2 : ∀x y, (∀u v : set α, is_open u → is_open v → x ∈ u → y ∈ v → ∃ r, r ∈ u ∩ v) → x = y)



import data.fintype

open equiv

instance thing {α β : Type*} [group α] [group β] [fintype α] [decidable_eq β] :
  decidable_pred (@is_group_hom α β _ _) :=
λ f, decidable_of_iff (∀ x y, f (x * y) = f x * f y)
⟨λ h, ⟨h⟩, λ ⟨h⟩, h⟩

lemma h : ¬is_group_hom ((^3) : perm (fin 4) → perm (fin 4)) := dec_trivial

#print fintype.equiv_fin

#eval list.find (λ x : perm (fin 4) × perm (fin 4),
  x.1 ^ 3 * x.2 ^ 3 ≠ (x.1 * x.2) ^ 3) (quot.unquot
  (finset.univ : finset (perm (fin 4) × perm (fin 4))).1)

#print h

#exit

class is_rat (x : ℝ) :=
(val : ℚ)
(val_eq : (val : ℝ) = x)

variables (x y : ℝ) [is_rat x] [is_rat y]
noncomputable theory

instance : is_rat (x + y) := ⟨is_rat.val x + is_rat.val y, by simp [is_rat.val_eq]⟩
instance : is_rat (x * y) := ⟨is_rat.val x * is_rat.val y, by simp [is_rat.val_eq]⟩
instance : is_rat (-x) := ⟨-is_rat.val x, by simp [is_rat.val_eq]⟩
instance : is_rat (x - y) := ⟨is_rat.val x - is_rat.val y, by simp [is_rat.val_eq]⟩
instance : is_rat (x / y) := ⟨is_rat.val x / is_rat.val y, by simp [is_rat.val_eq]⟩
instance : is_rat (x⁻¹) := ⟨(is_rat.val x)⁻¹, by simp [is_rat.val_eq]⟩
instance zero_is_rat : is_rat 0 := ⟨0, by simp [rat.cast_zero]⟩
instance one_is_rat : is_rat 1 := ⟨1, by simp⟩
instance : is_rat (bit0 x) := by unfold bit0; apply_instance
instance : is_rat (bit1 x) := by unfold bit1; apply_instance
instance i2 : decidable (x = y) :=
by rw [← is_rat.val_eq x, ← is_rat.val_eq y, rat.cast_inj]; apply_instance
instance i3 : decidable (x ≤ y) :=
by rw [← is_rat.val_eq x, ← is_rat.val_eq y, rat.cast_le]; apply_instance
instance i4 : decidable (x < y) :=
by rw [← is_rat.val_eq x, ← is_rat.val_eq y, rat.cast_lt]; apply_instance

lemma is_rat.val_inj {x y : ℝ} [is_rat x] [is_rat y] (h : is_rat.val x = is_rat.val y) : x = y :=
(is_rat.val_eq x).symm.trans (eq.trans (rat.cast_inj.2 h) (is_rat.val_eq y))
a ^ 2 + 3 * a - 1 = 0 ↔ (X ^ 2 + 3 * X - 1).eval a = 0
set_option profiler true
set_option class.instance_max_depth 100
instance i5 : is_rat ((5 : ℝ) / 4) := by apply_instance
#print as_true

#eval ( (5 : ℝ) * 4 = 10 * 2 : bool)

example : (5 : ℚ) / 2 = 10 / 4 := rfl
lemma l1 : (5 : ℝ) / 2 = 10 / 4 := is_rat.val_inj rfl



#print l1
#print l2

#exit

#exit
#print expr
open expr level
#print level
meta def level.repr : level → string
| zero       := "0"
| (succ l)   := level.repr l ++ "+1"
| (max a b)  := "max " ++ a.repr ++ " " ++ b.repr
| (imax a b) := "imax " ++ a.repr ++ " " ++ b.repr
| (param a)  := "param " ++ a.to_string
| (mvar a)   := "mvar " ++ a.to_string

meta instance : has_repr level := ⟨level.repr⟩

meta def expr.to_string' : expr → string
| (var a) := "var (" ++ repr a ++")"
| (sort a) := "sort (" ++ repr a ++")"
| (const a b) := "const (" ++ a.to_string ++ ") (" ++ repr b ++")"
| (expr.mvar a b c) := "mvar (" ++ a.to_string ++ ") (" ++ b.to_string ++ ")"
| (local_const a b c d) := "local_const (" ++ a.to_string ++ ") (" ++ b.to_string ++ ") (" ++
   expr.to_string' d ++")"
| (pi a b c d) := "pi (" ++ a.to_string ++") (" ++ expr.to_string' c  ++") (" ++ expr.to_string' d ++")"
| (lam a b c d) := "lam (" ++ a.to_string ++ ") (" ++ expr.to_string' c ++ ") (" ++ expr.to_string' d ++")"
| (app a b) := "app (" ++ expr.to_string' a ++ ") (" ++ expr.to_string b ++ ")"
| _ := "aargh"

def list.nil' : Π (α : Type), list α := @list.nil

def f : ℕ → ℕ := id

meta def x : tactic unit :=
do t ← tactic.infer_type `(f),
  tactic.trace (expr.to_string' t), tactic.skip

#eval (format.compose (format.of_string "a") (format.of_string "b")).to_string
#print expr.to_raw_fmt
#eval (`(fin) : expr).to_raw_fmt.to_string
#eval expr.to_string' `(fin)

#exit
import data.equiv.encodable algebra.group_power
#print encodable

-- #eval encodable.choose (show ∃ x : (ℤ × ℕ), x.1 ^ 2 + 615 = 2 ^ x.2, from ⟨(59, 12), rfl⟩)

#print tactic.interactive.rw
#print tactic.transparency
example : 2 = 1 + 1 := by tactic.reflexivity tactic.transparency.none
#print tactic.interactive.refl
example : 2 = list.sum [2] := by tactic.reflexivity tactic.transparency.semireducible

#exit
import data.polynomial
open polynomial
#eval (X ^ 2 + 3 * X - 4 : polynomial ℤ).comp (X ^ 3 - X)


example : (@with_top.add_monoid ℕ _) = (@add_comm_monoid.to_add_monoid (with_top ℕ) _) := rfl

variables {α β γ δ : Type} {f : α → β}

#check function.comp (@function.comp ℕ _ _) (@function.comp ℕ ℕ (ℕ → ℕ))
#check
#print infer_instance
@[derive decidable_eq] inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:51 := fml.not

inductive prf : fml → Type
| axk {p q} : prf (p →' q →' p)
| axs {p q r} : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX {p q} : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

instance (p): has_sizeof (prf p) := by apply_instance

open prf

meta def length {f : fml} (t : prf f) : ℕ :=
prf.rec_on t (λ _ _, 1) (λ _ _ _, 1) (λ _ _, 1) (λ _ _ _ _, (+))

instance (p q : fml) : has_coe_to_fun (prf (p →' q)) :=
{ F := λ x, prf p → prf q,
  coe := λ x y, mp y x }

lemma imp_self' (p : fml) : prf (p →' p) :=
mp (@axk p p) (mp axk axs)

lemma imp_comm {p q r : fml} (h : prf (p →' q →' r)) : prf (q →' p →' r) :=
mp axk (mp (mp (mp h axs) axk) (@axs _ (p →' q) _))

lemma imp_of_true (p : fml) {q : fml} (h : prf q) : prf (p →' q) :=
mp h axk

namespace prf
prefix `⊢ `:30 := prf

def mp' {p q} (h1 : ⊢ p →' q) (h2 : ⊢ p) : ⊢ q := mp h2 h1
def a1i {p q} : ⊢ p → ⊢ q →' p := mp' axk
def a2i {p q r} : ⊢ p →' q →' r → ⊢ (p →' q) →' p →' r := mp' axs
def con4i {p q} : ⊢ ¬' p →' ¬' q → ⊢ q →' p := mp' axX
def mpd {p q r} (h : ⊢ p →' q →' r) : ⊢ p →' q → ⊢ p →' r := mp' (a2i h)
def syl {p q r} (h1 : ⊢ p →' q) (h2 : ⊢ q →' r) : ⊢ p →' r := mpd (a1i h2) h1
def id {p} : ⊢ p →' p := mpd axk (@axk p p)
def a1d {p q r} (h : ⊢ p →' q) : ⊢ p →' r →' q := syl h axk
def com12 {p q r} (h : ⊢ p →' q →' r) : ⊢ q →' p →' r := syl (a1d id) (a2i h)
def con4d {p q r} (h : ⊢ p →' ¬' q →' ¬' r) : ⊢ p →' r →' q := syl h axX
def absurd {p q} : ⊢ ¬' p →' p →' q := con4d axk
def imidm {p q} (h : ⊢ p →' p →' q) : ⊢ p →' q := mpd h id
def contra {p} : ⊢ (¬' p →' p) →' p := imidm (con4d (a2i absurd))
def notnot2 {p} : ⊢ ¬' ¬' p →' p := syl absurd contra
def mpdd {p q r s} (h : ⊢ p →' q →' r →' s) : ⊢ p →' q →' r → ⊢ p →' q →' s := mpd (syl h axs)
def syld {p q r s} (h1 : ⊢ p →' q →' r) (h2 : ⊢ p →' r →' s) : ⊢ p →' q →' s := mpdd (a1d h2) h1
def con2d {p q r} (h1 : ⊢ p →' q →' ¬' r) : ⊢ p →' r →' ¬' q := con4d (syld (a1i notnot2) h1)
def con2i {p q} (h1 : ⊢ p →' ¬' q) : ⊢ q →' ¬' p := con4i (syl notnot2 h1)
def notnot1 {p} : ⊢ p →' ¬' ¬' p := con2i id
#eval length (@notnot1 (atom 0))

lemma notnot1' {p} : ⊢ p →' ¬' ¬' p :=
mp (mp (mp (mp axk (mp (mp axX axk) axs))
  (mp (mp (mp (mp axk (mp axk axs))
  (mp (mp (mp (mp axk (mp (mp axX axk) axs)) axs) (mp (mp axX axk) axs)) axs)) axk) axs))
     (mp (mp (mp axk (mp axk axs)) axk) axs)) axX

-- @mp ((¬' ¬' ¬' p) →' ¬' p) (p →' ¬' ¬' p)
--     (@mp ((¬' ¬' ¬' p) →' (¬' p) →' (¬' p) →' ¬' p) ((¬' ¬' ¬' p) →' ¬' p)
--        (@mp ((¬' p) →' (¬' p) →' ¬' p) ((¬' ¬' ¬' p) →' (¬' p) →' (¬' p) →' ¬' p)
--           (@axk (¬' p) (¬' p))
--           (@axk ((¬' p) →' (¬' p) →' ¬' p) (¬' ¬' ¬' p)))
--        (@mp ((¬' ¬' ¬' p) →' ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--           (((¬' ¬' ¬' p) →' (¬' p) →' (¬' p) →' ¬' p) →' (¬' ¬' ¬' p) →' ¬' p)
--           (@mp ((¬' ¬' ¬' p) →' (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--              ((¬' ¬' ¬' p) →' ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--              (@mp ((¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                 ((¬' ¬' ¬' p) →' (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                 (@mp ((¬' ¬' ¬' p) →' ¬' ¬' ¬' p)
--                    ((¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                    (@mp ((¬' ¬' ¬' p) →' (¬' ¬' ¬' p) →' ¬' ¬' ¬' p) ((¬' ¬' ¬' p) →' ¬' ¬' ¬' p)
--                       (@axk (¬' ¬' ¬' p) (¬' ¬' ¬' p))
--                       (@mp ((¬' ¬' ¬' p) →' ((¬' ¬' ¬' p) →' ¬' ¬' ¬' p) →' ¬' ¬' ¬' p)
--                          (((¬' ¬' ¬' p) →' (¬' ¬' ¬' p) →' ¬' ¬' ¬' p) →'
--                             (¬' ¬' ¬' p) →' ¬' ¬' ¬' p)
--                          (@axk (¬' ¬' ¬' p) ((¬' ¬' ¬' p) →' ¬' ¬' ¬' p))
--                          (@axs (¬' ¬' ¬' p) ((¬' ¬' ¬' p) →' ¬' ¬' ¬' p) (¬' ¬' ¬' p))))
--                    (@mp
--                       ((¬' ¬' ¬' p) →'
--                          (¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                       (((¬' ¬' ¬' p) →' ¬' ¬' ¬' p) →'
--                          (¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                       (@mp ((¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                          ((¬' ¬' ¬' p) →'
--                             (¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                          (@axk (¬' ¬' ¬' p) (¬' ¬' (¬' p) →' (¬' p) →' ¬' p))
--                          (@axk ((¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                             (¬' ¬' ¬' p)))
--                       (@axs (¬' ¬' ¬' p) (¬' ¬' ¬' p)
--                          ((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p))))
--                 (@mp
--                    ((¬' ¬' ¬' p) →'
--                       ((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p) →'
--                         (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                    (((¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p) →'
--                       (¬' ¬' ¬' p) →' (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                    (@mp
--                       (((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p) →'
--                          (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                       ((¬' ¬' ¬' p) →'
--                          ((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p) →'
--                            (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                       (@axX (¬' ¬' p) (¬' (¬' p) →' (¬' p) →' ¬' p))
--                       (@axk
--                          (((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p) →'
--                             (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                          (¬' ¬' ¬' p)))
--                    (@axs (¬' ¬' ¬' p) ((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                       ((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p))))
--              (@mp
--                 ((¬' ¬' ¬' p) →'
--                    ((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p) →'
--                      ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--                 (((¬' ¬' ¬' p) →' (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p) →'
--                    (¬' ¬' ¬' p) →' ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--                 (@mp
--                    (((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p) →'
--                       ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--                    ((¬' ¬' ¬' p) →'
--                       ((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p) →'
--                         ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--                    (@axX ((¬' p) →' (¬' p) →' ¬' p) (¬' p))
--                    (@axk
--                       (((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p) →'
--                          ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--                       (¬' ¬' ¬' p)))
--                 (@axs (¬' ¬' ¬' p) ((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                    (((¬' p) →' (¬' p) →' ¬' p) →' ¬' p))))
--           (@axs (¬' ¬' ¬' p) ((¬' p) →' (¬' p) →' ¬' p) (¬' p))))
--     (@axX p (¬' ¬' p))

-- set_option pp.implicit true

#print not_not_p_of_p

-- /-
-- example usage:
-- lemma p_of_p_of_p_of_q (p q : fml) : prf $ (p →' q) →' (p →' p) :=
-- begin
--   apply mp (p →' q →' p) ((p →' q) →' p →' p) (axk p q),
--   exact axs p q p
-- end
-- -/

-- theorem Q6b (p : fml) : prf $ p →' ¬' ¬' p := sorry

namespace prop_logic

-- infixr ` →' `:50 := imp
-- local notation ` ¬' ` := fml.not

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:51 := fml.not

--CAN I MAKE THIS A FUNCTION INTO PROP INSTEAD OF TYPE????
-- inductive thm : fml → Type
-- | axk (p q) : thm (p →' q →' p)
-- | axs (p q r) : thm $ (p →' q →' r) →' (p →' q) →' (p →' r)
-- | axn (p q) : thm $ ((¬' q) →' (¬' p)) →' p →' q
-- | mp {p q} : thm p → thm (p →' q) → thm q
-- open thm

lemma p_of_p (p : fml) : prf (p →' p) :=
mp (@axk p p) (mp axk axs)


inductive consequence (G : list fml) : fml → Type
| axk (p q) : consequence (p →' q →' p)
| axs (p q r) : consequence $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axn (p q) : consequence $ ((¬'q) →' (¬'p)) →' p →' q
| mp (p q) : consequence p → consequence (p →' q) → consequence q
| of_G (g ∈ G) : consequence g

lemma consequence_of_thm (f : fml) (H : prf f) (G : list fml) : consequence G f :=
begin
  induction H,
  exact consequence.axk G H_p H_q,
  exact consequence.axs G H_p H_q H_r,
  exact consequence.axn G H_p H_q,
  exact consequence.mp H_p H_q H_ih_a H_ih_a_1,
end

lemma thm_of_consequence_null (f : fml) (H : consequence [] f) : prf f :=
begin
  induction H,
  exact @axk H_p H_q,
  exact @axs H_p H_q H_r,
  exact @axX H_p H_q,
  exact mp H_ih_a H_ih_a_1,
  exact false.elim (list.not_mem_nil H_g H_H),
end

theorem deduction (G : list fml) (p q : fml) (H : consequence (p :: G) q) : consequence G (p →' q) :=
begin
  induction H,
  have H1 := consequence.axk G H_p H_q,
  have H2 := consequence.axk G (H_p →' H_q →' H_p) p,
  exact consequence.mp _ _ H1 H2,
  have H6 := consequence.axs G H_p H_q H_r,
  have H7 := consequence.axk G ((H_p →' H_q →' H_r) →' (H_p →' H_q) →' H_p →' H_r) p,
  exact consequence.mp _ _ H6 H7,
  have H8 := consequence.axn G H_p H_q,
  have H9 := consequence.axk G (((¬' H_q) →' ¬' H_p) →' H_p →' H_q) p,
  exact consequence.mp _ _ H8 H9,
  have H3 := consequence.axs G p H_p H_q,
  have H4 := consequence.mp _ _ H_ih_a_1 H3,
  exact consequence.mp _ _ H_ih_a H4,
  rw list.mem_cons_iff at H_H,
  exact if h : H_g ∈ G then
  begin
    have H51 := consequence.of_G H_g h,
    have H52 := consequence.axk G H_g p,
    exact consequence.mp _ _ H51 H52,
  end else
  begin
    have h := H_H.resolve_right h,
    rw h,
    exact consequence_of_thm _ (p_of_p p) G,
  end
end

lemma part1 (p : fml) : consequence [¬' (¬' p)] p :=
begin
  have H1 := consequence.axk [¬' (¬' p)] p p,
  have H2 := consequence.axk [¬' (¬' p)] (¬' (¬' p)) (¬' (¬' (p →' p →' p))),
  have H3 := consequence.of_G (¬' (¬' p)) (list.mem_singleton.2 rfl),
  have H4 := consequence.mp _ _ H3 H2,
  have H5 := consequence.axn [¬' (¬' p)] (¬' p) (¬' (p →' p →' p)),
  have H6 := consequence.mp _ _ H4 H5,
  have H7 := consequence.axn [¬' (¬' p)] (p →' p →' p) p,
  have H8 := consequence.mp _ _ H6 H7,
  exact consequence.mp _ _ H1 H8,
end

lemma part1' (p : fml) : prf (¬' ¬' p →' p) :=
begin
  have H1 := @axk p p,
  have H2 := @axk (¬' ¬' p) (¬' ¬' (p →' p →' p)),
  have H3 := imp_self' (¬' ¬' p),
  have H4 := mp H3 H2,

end

lemma p_of_not_not_p (p : fml) : thm ((¬' (¬' p)) →' p) :=
begin
  have H1 := deduction [] (¬' (¬' p)) p,

  have H2 := H1 (part1 p),
  exact thm_of_consequence_null ((¬' (¬' p)) →' p) H2,
end

theorem not_not_p_of_p (p : fml) : thm (p →' (¬' (¬' p))) :=
begin
  have H1 := thm.axn p (¬' (¬' p)),
  have H2 := p_of_not_not_p (¬' p),
  exact thm.mp H2 H1,
end
set_option pp.implicit true
#reduce not_not_p_of_p

theorem not_not_p_of_p' (p : fml) : thm (p →' (¬' (¬' p))) :=
thm.mp
    (thm.mp (thm.mp (thm.axk (¬' p) (¬' p)) (thm.axk (¬' p →' ¬' p →' ¬' p) (¬' (¬' (¬' p)))))
       (thm.mp
          (thm.mp
             (thm.mp
                (thm.mp
                   (thm.mp (thm.axk (¬' (¬' (¬' p))) (¬' (¬' (¬' p))))
                      (thm.mp (thm.axk (¬' (¬' (¬' p))) (¬' (¬' (¬' p)) →' ¬' (¬' (¬' p))))
                         (thm.axs (¬' (¬' (¬' p))) (¬' (¬' (¬' p)) →' ¬' (¬' (¬' p))) (¬' (¬' (¬' p))))))
                   (thm.mp
                      (thm.mp (thm.axk (¬' (¬' (¬' p))) (¬' (¬' (¬' p →' ¬' p →' ¬' p))))
                         (thm.axk
                            (¬' (¬' (¬' p)) →' ¬' (¬' (¬' p →' ¬' p →' ¬' p)) →' ¬' (¬' (¬' p)))
                            (¬' (¬' (¬' p)))))
                      (thm.axs (¬' (¬' (¬' p))) (¬' (¬' (¬' p)))
                         (¬' (¬' (¬' p →' ¬' p →' ¬' p)) →' ¬' (¬' (¬' p))))))
                (thm.mp
                   (thm.mp (thm.axn (¬' (¬' p)) (¬' (¬' p →' ¬' p →' ¬' p)))
                      (thm.axk
                         ((¬' (¬' (¬' p →' ¬' p →' ¬' p)) →' ¬' (¬' (¬' p))) →'
                            ¬' (¬' p) →' ¬' (¬' p →' ¬' p →' ¬' p))
                         (¬' (¬' (¬' p)))))
                   (thm.axs (¬' (¬' (¬' p))) (¬' (¬' (¬' p →' ¬' p →' ¬' p)) →' ¬' (¬' (¬' p)))
                      (¬' (¬' p) →' ¬' (¬' p →' ¬' p →' ¬' p)))))
             (thm.mp
                (thm.mp (thm.axn (¬' p →' ¬' p →' ¬' p) (¬' p))
                   (thm.axk
                      ((¬' (¬' p) →' ¬' (¬' p →' ¬' p →' ¬' p)) →'
                         (¬' p →' ¬' p →' ¬' p) →' ¬' p)
                      (¬' (¬' (¬' p)))))
                (thm.axs (¬' (¬' (¬' p))) (¬' (¬' p) →' ¬' (¬' p →' ¬' p →' ¬' p))
                   ((¬' p →' ¬' p →' ¬' p) →' ¬' p))))
          (thm.axs (¬' (¬' (¬' p))) (¬' p →' ¬' p →' ¬' p) (¬' p))))
    (thm.axn p (¬' (¬' p)))

#exit
@[derive decidable_eq] inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:40 := fml.not

inductive prf : fml → Type
| axk (p q) : prf (p →' q →' p)
| axs (p q r) : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX (p q) : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

#print prf.rec

open prf

/-
-- example usage:
lemma p_of_p_of_p_of_q (p q : fml) : prf $ (p →' q) →' (p →' p) :=
begin
  apply mp (p →' q →' p) ((p →' q) →' p →' p) (axk p q),
  exact axs p q p
end
-/

def is_not : fml → Prop :=
λ f, ∃ g : fml, f = ¬' g

#print prf.rec_on
theorem Q6b (f : fml) (p : prf f) : is_not f → false :=
begin
  induction p,
  {admit},
  {admit},
  {admit},
  {
    clear p_ih_a_1,
    }


end

#print Q6b

theorem Q6b : ∀ p : fml, ¬(prf $ p →' ¬' ¬' p) :=
begin
  cases p,


end


#exit

import data.fintype

section

@[derive decidable_eq] inductive cbool
| t : cbool
| f : cbool
| neither : cbool
open cbool

instance : fintype cbool := ⟨{t,f,neither}, λ x, by cases x; simp⟩

variables (imp : cbool → cbool → cbool) (n : cbool → cbool)
  (a1 : ∀ p q, imp p (imp q p) = t)
  (a2 : ∀ p q, imp (imp (n q) (n p)) (imp p q) = t)
  (a3 : ∀ p q r, imp (imp p (imp q r)) (imp (imp p q) (imp p r)) = t)
include a1 a2 a3

set_option class.instance_max_depth 50

-- example : ∀ p, imp p (n (n p)) = t :=
-- by revert imp n; exact dec_trivial



end

open finset

instance inst1 : has_repr (bool → bool) :=
⟨λ f, "(tt ↦ " ++ repr (f tt) ++ ", ff ↦ " ++ repr (f ff) ++")"⟩

instance inst2 : has_repr (bool → bool → bool) :=
⟨λ f, "(tt ↦ " ++ repr (f tt) ++ ", ff ↦ " ++ repr (f ff)++")"⟩

#eval band

#eval (((univ : finset ((bool → bool → bool) × (bool → bool))).filter
  (λ x : (bool → bool → bool) × (bool → bool),
    (∀ p q, x.1 p (x.1 q p) = tt) ∧
    (∀ p q, x.1 (x.1 (x.2 q) (x.2 p)) (x.1 p q) = tt) ∧
    (∀ p q r, x.1 (x.1 p (x.1 q r)) (x.1 (x.1 p q) (x.1 p r)) = tt)))


#exit
import ring_theory.ideals

variables {p : Prop} {α : Type*} [comm_ring α]

instance : is_ideal {x : α | x = 0 ∨ p} :=
{ to_is_submodule :=
  ⟨or.inl rfl,
    λ x y hx hy, hx.elim (λ hx0, by rw [hx0, zero_add]; exact hy) or.inr,
    λ c x hx, hx.elim (λ hx0, by rw [hx0, smul_eq_mul, mul_zero]; exact or.inl rfl) or.inr⟩ }

def h : is_ideal {x : ℤ | x = 0 ∨ p} := by apply_instance
set_option pp.implicit true
#print axioms set_of.is_ideal
#print axioms nonzero_comm_ring.to_comm_ring

#exit
import algebra.pi_instances

variables {G₁ G₂ G₃ : Type} [group G₁] [group G₂] [group G₃]

def isom : {f : (G₁ × (G₂ × G₃)) ≃ ((G₁ × G₂) × G₃) // is_group_hom f} :=
⟨⟨λ ⟨a, ⟨b, c⟩⟩, ⟨⟨a, b⟩, c⟩, λ ⟨⟨a, b⟩, c⟩, ⟨a, b, c⟩, λ ⟨_, _, _⟩, rfl, λ ⟨⟨_, _⟩, _⟩, rfl⟩, ⟨λ ⟨_, _, _⟩ ⟨_, _, _⟩, rfl⟩⟩



#exit
import data.equiv.denumerable
open denumerable
#eval of_nat (ℤ × ℤ) 145903

#exit
import data.polynomial ring_theory.ideals
open polynomial euclidean_domain

def gaussian_integers := @quotient_ring.quotient (polynomial ℤ) _
  (span ({(X : polynomial ℤ) ^ 2 + 1} : set (polynomial ℤ)))
  (is_ideal.span ({X ^ 2 + 1} : set (polynomial ℤ)))

instance : decidable_eq gaussian_integers :=
λ x y, begin  end




#eval gcd_a (-5 : ℤ) (-11)

local notation `f` := ((X : polynomial ℚ) ^ 2 * C (53/96) - 22 * X - 141)
local notation `g` := (23 * (X : polynomial ℚ) ^ 3 -  44 * X^2 + 3 * X - 2)

#eval (5 / 4 : ℚ)
#eval gcd_a f g * C (coeff (gcd f g) 0)⁻¹
#eval gcd f g
#eval (f * (gcd_a f g * C (coeff (gcd f g) 0)⁻¹) - 1) % g




#exit
import data.nat.choose data.nat.prime
open nat

lemma prime_dvd_fact_iff : ∀ {n p : ℕ} (hp : prime p), p ∣ n.fact ↔ p ≤ n
| 0 p hp := by simp [nat.pos_iff_ne_zero.1 hp.pos, ne.symm (ne_of_lt hp.gt_one)]
| (n+1) p hp := begin
  rw [fact_succ, hp.dvd_mul, prime_dvd_fact_iff hp],
  exact ⟨λ h, h.elim (le_of_dvd (succ_pos _)) le_succ_of_le,
    λ h, (lt_or_eq_of_le h).elim (or.inr ∘ le_of_lt_succ) (λ h, by simp [h])⟩
end

example {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : prime p) : p ∣ choose p k :=
(hp.dvd_mul.1 (show p ∣ choose p k * (fact k * fact (p - k)),
  by rw [← mul_assoc, choose_mul_fact_mul_fact (le_of_lt hkp)];
    exact dvd_fact hp.pos (le_refl _))).resolve_right
      (by rw [hp.dvd_mul, prime_dvd_fact_iff hp,
          prime_dvd_fact_iff hp, not_or_distrib, not_le, not_le];
        exact ⟨hkp, nat.sub_lt_self hp.pos hk⟩)



#exit
#print eq

inductive Id {α : Type} (x : α) : α → Type
| refl : Id x

lemma T1 {α : Type} (x y : α) (i j : Id x y) : i = j :=
by cases i; cases j; refl
#print T1

#reduce T1

lemma T2 {α : Type} (x y : α) (i j : Id x y) : Id i j :=
begin cases i; cases j; constructor end

#print T2

#exit
import group_theory.quotient_group analysis.topology.topological structures

instance {α : Type*} [topological_group α] (S : set α) [normal_subgroup S] :
  topological_space (quotient_group.quotient S) := by apply_instance

#exit

import analysis.real tactic.linarith

open real filter

lemma IVT {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x, a ≤ x → x ≤ b → tendsto f (nhds x) (nhds (f x)))
  (ha : f a ≤ 0) (hb : 0 ≤ f b) (hab : a ≤ b) : ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ f x = 0 :=
let x := Sup {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b} in
have hx₁ : ∃ y, ∀ g ∈ {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b}, g ≤ y := ⟨b, λ _ h, h.2.2⟩,
have hx₂ : ∃ y, y ∈ {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b} := ⟨a, ha, le_refl _, hab⟩,
have hax : a ≤ x, from le_Sup _ hx₁ ⟨ha, le_refl _, hab⟩,
have hxb : x ≤ b, from (Sup_le _ hx₂ hx₁).2 (λ _ h, h.2.2),
⟨x, hax, hxb,
  eq_of_forall_dist_le $ λ ε ε0,
    let ⟨δ, hδ0, hδ⟩ := tendsto_nhds_of_metric.1 (hf _ hax hxb) ε ε0 in
    (le_total 0 (f x)).elim
      (λ h, le_of_not_gt $ λ hfε, begin
        rw [dist_0_eq_abs, abs_of_nonneg h] at hfε,
        refine mt (Sup_le {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b} hx₂ hx₁).2
          (not_le_of_gt (sub_lt_self x (half_pos hδ0)))
          (λ g hg, le_of_not_gt
            (λ hgδ, not_lt_of_ge hg.1
              (lt_trans (sub_pos_of_lt hfε) (sub_lt_of_sub_lt
                (lt_of_le_of_lt (le_abs_self _) _))))),
        rw abs_sub,
        exact hδ (abs_sub_lt_iff.2 ⟨lt_of_le_of_lt (sub_nonpos.2 (le_Sup _ hx₁ hg)) hδ0,
          by simp only [x] at *; linarith⟩)
        end)
      (λ h, le_of_not_gt $ λ hfε, begin
        rw [dist_0_eq_abs, abs_of_nonpos h] at hfε,
        exact mt (le_Sup {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b})
          (λ h : ∀ k, k ∈ {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b} → k ≤ x,
            not_le_of_gt ((lt_add_iff_pos_left x).2 (half_pos hδ0))
              (h _ ⟨le_trans (le_sub_iff_add_le.2 (le_trans (le_abs_self _)
                    (le_of_lt (hδ $ by rw [dist_eq, add_sub_cancel, abs_of_nonneg (le_of_lt (half_pos hδ0))];
                      exact half_lt_self hδ0))))
                  (le_of_lt (sub_neg_of_lt hfε)),
                le_trans hax (le_of_lt ((lt_add_iff_pos_left _).2 (half_pos hδ0))),
                le_of_not_gt (λ hδy, not_lt_of_ge hb (lt_of_le_of_lt (show f b ≤ f b - f x - ε, by linarith)
                  (sub_neg_of_lt (lt_of_le_of_lt (le_abs_self _)
                    (@hδ b (abs_sub_lt_iff.2 ⟨by simp only [x] at *; linarith,
                      by linarith⟩))))))⟩))
          hx₁
        end)⟩

#print IVT

#exit
import tactic.norm_num tactic.ring tactic.linarith

lemma h (x y z : ℤ) (h₁ : 0 ≤ x) (h₂ : y + x ≤ z) : y ≤ z :=
by linarith

#print h

open nat

lemma prime_seven : prime 7 := by norm_num

#print prime_seven

lemma ring_thing (x y z : ℤ) : x ^ 2 - x * (y - z) - z * x = x * (x - y) := by ring

#print ring_thing

example (x : ℤ) (h : ∃ y, x = y ∧ x ^ 2 = 2)  :
open nat zmodp

lemma p7 : prime 7 := by norm_num

theorem foo (x y : zmodp 7 p7) (h : x ≠ y) : (x - y) ^ 6 = 1 :=
fermat_little p7 (sub_ne_zero.2 h)

#exit
import data.polynomial
import linear_algebra.multivariate_polynomial
import ring_theory.associated

universe u

namespace algebraic_closure

variables (k : Type u) [field k] [decidable_eq k]

def irred : set (polynomial k) :=
{ p | irreducible p }

def big_ring : Type u :=
mv_polynomial (irred k) k

instance : comm_ring (big_ring k) :=
mv_polynomial.comm_ring

instance : module (big_ring k) (big_ring k) := by apply_instance

instance : decidable_eq (big_ring k) := by apply_instance

instance foo : decidable_eq (irred k) := by apply_instance

set_option profiler true
def big_ideal : set (big_ring k) :=
span (⋃ p : irred k, { polynomial.eval₂ (@mv_polynomial.C k (irred k) _ _ _)
  (@mv_polynomial.X k (irred k) _ _ _ p) p.1 })

#exit
import data.nat.basic

#print dlist

@[simp] lemma nat.strong_rec_on_beta {p : nat → Sort*} : ∀ (n : nat) (h : ∀ n, (∀ m, m < n → p m) → p n),
  (nat.strong_rec_on n h : p n) = h n (λ m H, nat.strong_rec_on m h)
| 0 h := begin simp [nat.strong_rec_on, or.by_cases], congr, funext,
  exact (nat.not_lt_zero _ h₁).elim, intros, end

#exit
meta def foo (n : ℕ) : option ℕ :=
do let m : ℕ :=
  match n with
  | 0     := 1
  | (n+1) := by exact _match n + _match n
  end,
return m
#print foo
#eval foo 4 -- some 16



-- begin
--   let m : ℕ :=
--   match n with
--   | 0     := 1
--   | (n+1) := _match n + _match n
--   end,
--   have h : m = 2 ^ n, by induction n;
--     simp [nat.mul_succ, nat.succ_mul, *, m, _example._match_1, nat.pow_succ] at *,

-- end


import set_theory.cardinal
#print list.zip_with
open cardinal

example (α : Type*) (S T : set α)
  (HS : set.finite S) (HT : set.finite T)
  (H : finset.card (set.finite.to_finset HS) ≤ finset.card (set.finite.to_finset HT)) :
  cardinal.mk S ≤ cardinal.mk T :=
begin
  haveI := classical.choice HS,
  haveI := classical.choice HT,
  rwa [fintype_card S, fintype_card T, nat_cast_le,
    set.card_fintype_of_finset' (set.finite.to_finset HS),
    set.card_fintype_of_finset' (set.finite.to_finset HT)];
  simp
end



example (f g : ℕ → ℕ) : (∀ x : ℕ, f x = g x) → f ≈ g := id
#print funext

#exit
import data.nat.modeq tactic.find

example (p : ℕ) (nine : 2 ∣ p / 2) (thing11 : 3 + 4 * (p / 4) = p) : false :=
begin
  rw [nat.dvd_iff_mod_eq_zero, ← nat.mod_mul_right_div_self,
    ← thing11, show 2 * 2 = 4, from rfl, nat.add_mul_mod_self_left] at nine,
  contradiction


end
#exit
import data.list.sort data.string

meta def list_constant (e : expr) : rbtree name :=
e.fold (mk_rbtree name) $ λ e _ cs,
let n := e.const_name in
if e.is_constant
then cs.insert n
else cs

open declaration tactic

meta def const_in_def (n : name) : tactic (list name) :=
do d ← get_decl n,
match d with
| thm _ _ t v      := return (list_constant v.get ∪ list_constant t)
| defn _ _ t v _ _ := return (list_constant v ∪ list_constant t)
| cnst _ _ t _     := return (list_constant t)
| ax _ _ t         := return (list_constant t)
end

meta def const_in_def_trans_aux : list name × list (name × list name) →
  tactic (list name × list (name × list name))
| ([], l₂) := pure ([], l₂)
| (l₁, l₂) :=
do l' ← l₁.mmap (λ n, do l ← const_in_def n, return (n, l)),
let l2 := l' ++ l₂,
const_in_def_trans_aux ((l'.map prod.snd).join.erase_dup.diff (l2.map prod.fst), l2)

meta def const_in_def_trans (n : name) : tactic unit :=
do l ← const_in_def_trans_aux ([n], []),
trace l.2.length,
trace (list.insertion_sort (≤) (l.2.map to_string)),
return ()

meta def list_all_consts : tactic (list name) :=
do e ← get_env,
let l : list name := environment.fold e []
  (λ d l, match d with
    | thm n _ _ _ := n :: l
    | defn n _ _ _ _ _ := n :: l
    | cnst n _ _ _ := n :: l
    | ax n _ _ := n :: l end),
trace l,
trace l.length,
return l

meta def trans_def_all_aux : list name → rbmap name (rbtree name)
  → rbmap name (rbtree name) → option (rbmap name (rbtree name))
| []      m₁ m₂ := pure m₂
| (n::l₁) m₁ m₂ :=
do l₁ ← m₁.find n,
l₂ ← l₁.mmap m₁.find,
let l₃ := l₂.join,
if l₃ = l₁ then trans_def_all_aux l₁ (m₁.erase n)
else sorry



meta def trans_def_list (l : list name) : tactic unit :=
do
map ← l.mmap (λ n, do l' ← const_in_def n, return (n, l)),
m ← trans_def_all_aux [`prod.swap] (pure (rbmap.from_list map)),
let result := m.to_list,
trace (result.map (λ n, (n.1, n.2.length))),
return ()

meta def trans_def_list_all : tactic unit :=
do l ← list_all_consts,
trans_def_list l,
return ()

#eval const_in_def_trans `prod.swap

-- #eval trans_def_list_all


#exit

#print list.union
meta def const_in_def_trans_aux : Π (n : name), tactic (list name)
| n := do d ← get_decl n,
match d with
| thm _ _ t v := do
  let v := v.get,
  let l := list_constant v,
--  do m ← l.mmap const_in_def_trans_aux,
  return (l).erase_dup
| defn _ _ t v _ _ := do
  let l := list_constant v,
  do m ← l.mmap const_in_def_trans_aux,
  return (l).erase_dup
| d := pure []
end

meta def const_in_def_depth_aux : ℕ → name → list name → tactic (list name)
| 0     n p := pure []
| (m+1) n p :=
do d ← get_decl n,
match d with
| thm _ _ t v := do
  let v := v.get,
  let l := (list_constant v).diff p,
  let q := p ++ l,
  l' ← l.mmap (λ n, const_in_def_depth_aux m n q),
  return (l ++ l'.bind id).erase_dup
| defn _ _ t v _ _ := do
  let l := (list_constant v).diff p,
  let q := p ++ l,
  l' ← l.mmap (λ n, const_in_def_depth_aux m n q),
  return (l ++ l'.bind id).erase_dup
| d := pure []
end



meta def const_in_def_depth_aux' : ℕ → Π n : name, tactic (list name)
| 0     n := pure []
| (m+1) n :=
do d ← get_decl n,
match d with
| thm _ _ t v := do
  let v := v.get,
  let l := list_constant v,
  l' ← l.mmap (const_in_def_depth_aux' m),
  return (l'.bind id ++ l).erase_dup
| defn _ _ t v _ _ := do
  let l := list_constant v,
  l' ← l.mmap (const_in_def_depth_aux' m),
  return (l'.bind id ++ l).erase_dup
| d := pure []
end

meta def const_in_def_depth (m : ℕ) (n : name) : tactic unit :=
do l ← const_in_def_depth_aux m n [],
  trace l.length,
  trace l,
  return ()

meta def const_in_def_depth' (m : ℕ) (n : name) : tactic unit :=
do l ← const_in_def_depth_aux' m n,
  trace l.length,
  trace l,
  return ()

meta def const_in_def_trans (n : name) : tactic unit :=
do l ← const_in_def_trans_aux n,
  trace l.length,
  trace l,
  return ()

set_option profiler true

-- #eval const_in_def_depth' 3 `polynomial.euclidean_domain

-- #eval const_in_def_depth 5 `polynomial.euclidean_domain



-- meta def const_in_def₂  (n : name) : tactic (list name) :=
-- do l ← const_in_def n,
-- m ← l.mmap const_in_def,
-- trace m,
-- return l
#print simp_config

#exit
 data.zmod.basic data.polynomial tactic.norm_num data.rat.basic

instance h {p : ℕ} (hp : nat.prime p) : has_repr (zmodp p hp) := fin.has_repr _

open polynomial
#eval (11 * X ^ 20 + 7 * X ^ 9 + 12 * X + 11 :
  polynomial ℚ) / (22 * X ^ 2 - 1)


#exit
import algebra.big_operators

open finset

lemma prod_involution (s : finset β) {f : β → α} :
  ∀ (g : Π a ∈ s, β)
  (h₁ : ∀ a ha, f a * f (g a ha) = 1)
  (h₂ : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
  (h₃ : ∀ a ha, g a ha ∈ s)
  (h₄ : ∀ a ha, g (g a ha) (h₃ a ha) = a),
  s.prod f = 1 :=
by haveI := classical.dec_eq β;
haveI := classical.dec_eq α; exact
finset.strong_induction_on s
  (λ s ih g h₁ h₂ h₃ h₄,
    if hs : s = ∅ then hs.symm ▸ rfl
    else let ⟨x, hx⟩ := exists_mem_of_ne_empty hs in
      have hmem : ∀ y ∈ (s.erase x).erase (g x hx), y ∈ s,
        from λ y hy, (mem_of_mem_erase (mem_of_mem_erase hy)),
      have g_inj : ∀ {x hx y hy}, g x hx = g y hy → x = y,
        from λ x hx y hy h, by rw [← h₄ x hx, ← h₄ y hy]; simp [h],
      have ih': (erase (erase s x) (g x hx)).prod f = (1 : α) :=
        ih ((s.erase x).erase (g x hx))
          ⟨subset.trans (erase_subset _ _) (erase_subset _ _),
            λ h, not_mem_erase (g x hx) (s.erase x) (h (h₃ x hx))⟩
          (λ y hy, g y (hmem y hy))
          (λ y hy, h₁ y (hmem y hy))
          (λ y hy, h₂ y (hmem y hy))
          (λ y hy, mem_erase.2 ⟨λ (h : g y _ = g x hx), by simpa [g_inj h] using hy,
            mem_erase.2 ⟨λ (h : g y _ = x),
              have y = g x hx, from h₄ y (hmem y hy) ▸ by simp [h],
              by simpa [this] using hy, h₃ y (hmem y hy)⟩⟩)
          (λ y hy, h₄ y (hmem y hy)),
      if hx1 : f x = 1
      then ih' ▸ eq.symm (prod_subset hmem
        (λ y hy hy₁,
          have y = x ∨ y = g x hx, by simp [hy] at hy₁; tauto,
          this.elim (λ h, h.symm ▸ hx1)
            (λ h, h₁ x hx ▸ h ▸ hx1.symm ▸ (one_mul _).symm)))
      else by rw [← insert_erase hx, prod_insert (not_mem_erase _ _),
        ← insert_erase (mem_erase.2 ⟨h₂ x hx hx1, h₃ x hx⟩),
        prod_insert (not_mem_erase _ _), ih', mul_one, h₁ x hx])

lemma prod_univ_units_finite_field {α : Type*} [fintype α] [field α] [decidable_eq α] : univ.prod (λ x, x) = (-1 : units α) :=
have h₁ : ∀ x : units α, x ∈ (univ.erase (-1 : units α)).erase 1 → x⁻¹ ∈ (univ.erase (-1 : units α)).erase 1,
  from λ x, by rw [mem_erase, mem_erase, mem_erase, mem_erase, ne.def, ne.def, ne.def,
    ne.def, inv_eq_iff_inv_eq, one_inv, inv_eq_iff_inv_eq]; simp; cc,
have h₂ : ∀ x : units α, x ∈ (univ.erase (-1 : units α)).erase 1 → x⁻¹ ≠ x,
  from λ x, by  rw [ne.def, units.inv_eq_self_iff]; finish,
calc univ.prod (λ x, x) = (insert (1 : units α) (insert (-1 : units α) ((univ.erase (-1 : units α)).erase 1))).prod (λ x, x) :
  by congr; simp [finset.ext]; tauto
... = -((univ.erase (-1 : units α)).erase 1).prod (λ x, x) :
  if h : (1 : units α) = -1
  then by rw [insert_eq_of_mem, prod_insert]; simp *; cc
  else by rw [prod_insert, prod_insert]; simp *
... = -1 : by rw [prod_finset_distinct_inv h₁ h₂]
#exit
import data.equiv.basic
variables {α : Type*} {β : Type*} [preorder α] [preorder β]

example (f : α ≃ β) (hf : ∀ a b, a ≤ b → f a ≤ f b)
  (hf' : ∀ a b, a ≤ b → f.symm a ≤ f.symm b) : ∀ a b, a < b ↔ f a < f b :=
have ∀ a b, a ≤ b ↔ f a ≤ f b, from λ a b,
⟨hf a b, λ h, by rw [← equiv.inverse_apply_apply f a, ← equiv.inverse_apply_apply f b];
  exact hf' (f a) (f b) h⟩,
λ a b, by simp [lt_iff_le_not_le, this]

#exit
import analysis.real




def g : topological_space ℝ := by apply_instance


theorem nonethm {t} : (none <|> none)=@none t := rfl

#exit
import data.nat.basic data.fintype algebra.group_power

instance nat.decidable_bexists_lt (n : ℕ) (P : Π k < n, Prop)
  [∀ k h, decidable (P k h)] : decidable (∃ k h, P k h) :=
decidable_of_iff (¬ ∀ k h, ¬ P k h) $ by simp [classical.not_forall]

instance nat.decidable_bexists_le (n : ℕ) (P : Π k ≤ n, Prop)
  [∀ k h, decidable (P k h)] : decidable (∃ k h, P k h) :=
decidable_of_iff (∃ (k) (h : k < n.succ), P k (nat.le_of_lt_succ h))
  ⟨λ ⟨k, hk, h⟩, ⟨k, nat.le_of_lt_succ hk, h⟩,
  λ ⟨k, hk, h⟩, ⟨k, nat.lt_succ_of_le hk, h⟩⟩

instance decidable_mul_self_nat (n : ℕ) : decidable (∃ k, k * k = n) :=
decidable_of_iff (∃ k ≤ n, k * k = n)
⟨λ ⟨k, h1, h2⟩, ⟨k, h2⟩, λ ⟨k, h1⟩, ⟨k, h1 ▸ nat.le_mul_self k, h1⟩⟩

instance decidable_sqr_nat (n : ℕ) : decidable (∃ k, k^2 = n) :=
decidable_of_iff (∃ k, k * k = n)
⟨λ ⟨k, h⟩, ⟨k, by rwa [nat.pow_two]⟩, λ ⟨k, h⟩, ⟨k, by rwa [nat.pow_two] at h⟩⟩

instance decidable_mul_self_int : Π (n : ℤ), decidable (∃ k, k * k = n)
| (int.of_nat n) := decidable_of_iff (∃ k, k * k = n)
    ⟨λ ⟨k, hk⟩, ⟨k, by rw [← int.coe_nat_mul, hk]; refl⟩,
    λ ⟨k, hk⟩, ⟨int.nat_abs k, by rw [← int.nat_abs_mul, hk]; refl⟩⟩
| -[1+ n] := is_false $ λ ⟨k, h1⟩, not_lt_of_ge (mul_self_nonneg k) $
    h1.symm ▸ int.neg_succ_of_nat_lt_zero n

instance decidable_sqr_int (n : ℤ) : decidable (∃ k, k^2 = n) :=
decidable_of_iff (∃ k, k * k = n)
⟨λ ⟨k, h⟩, ⟨k, by rwa [pow_two]⟩, λ ⟨k, h⟩, ⟨k, by rwa [pow_two] at h⟩⟩

theorem what_i_need: ¬ (∃ n : ℤ , n ^ 2 = 2 ) := dec_trivial

#exit
import data.polynomial data.rat.basic tactic.ring
open polynomial nat

def gcd' : ℕ → ℕ → ℕ
| 0        y := y
| (succ x) y := have y % succ x < succ x, from classical.choice ⟨mod_lt _ $ succ_pos _⟩,
                gcd (y % succ x) (succ x)

set_option pp.proofs true
#reduce (classical.choice (show nonempty true, from ⟨trivial⟩))

#print list.foldr
#print char
#eval (X ^ 17 + 2 * X + 1 : polynomial ℚ) / (17 * X ^ 9 + - 21/17 * X ^ 14 - 5 * X ^ 4 * 5)

example : (-17/21 * X ^ 3 : polynomial ℚ) = sorry

#eval ((1/17 * X ^ 8 + -25/289 * X ^ 3 : polynomial ℚ) =
  (C (1/17) * X ^ 8 + C (-25/289) * X ^ 3 : polynomial ℚ) : bool)

example : (1/17 * X ^ 8 + -25/289 * X ^ 3 : polynomial ℚ) =
  (C (1/17) * X ^ 8 + C -25 X ^ 3 : polynomial ℚ) := begin
  ℤ

end

example : (X ^ 2 + 2 * X + 1 : polynomial ℤ) %ₘ (X + 1) = 0 :=
(dvd_iff_mod_by_monic_eq_zero dec_trivial).2 ⟨X + 1, by ring⟩


#exit
import data.zmod

instance h (m : ℤ) : decidable (∃ n : ℤ, n ^ 2 = m) :=
decidable_of_iff (0 ≤ m ∧ m.nat_abs.sqrt ^ 2 = m.nat_abs)
⟨λ h, ⟨nat.sqrt m.nat_abs, by rw [← int.coe_nat_pow, h.2, int.nat_abs_of_nonneg h.1]⟩,
 λ ⟨s, hs⟩, ⟨hs ▸ (pow_two_nonneg _), by rw [← hs, pow_two, int.nat_abs_mul, nat.sqrt_eq, nat.pow_two]⟩⟩

#eval (∄ n : ℤ, n ^ 2 = 2 : bool)
#print nat.gcd._main._pack
example : nat.gcd 4 5 = 1 := rfl

lemma two_not_square : ∄ n : ℤ, n ^ 2 = 2 := dec_trivial

example : ∄ n : ℤ, n ^ 2 = 2 :=
λ ⟨n, hn⟩, have h : ∀ n : zmod 3, n ^ 2 ≠ (2 : ℤ), from dec_trivial,
by have := h n; rw ← hn at this; simpa


example (d : ℤ) : d * d ≡ 0 [ZMOD 8] ∨ d * d ≡ 1 [ZMOD 8] ∨ d * d ≡ 4 [ZMOD 8] :=
have ∀ d : zmod 8, d * d = (0 : ℤ) ∨ d * d = (1 : ℤ) ∨ d * d = (4 : ℤ), from dec_trivial,
by have := this d;
  rwa [← int.cast_mul, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int] at this

example (a b : ℤ) (h : a ≡ b [ZMOD 8]) : a ^ 2 ≡ b ^ 2 [ZMOD 8] :=
by rw [pow_two, pow_two]; exact int.modeq.modeq_mul h h

example : ∀ a b : zmod 8, a = b → a ^ 2 = b ^ 2 := dec_trivial



open finset
def thing : ℕ → Type := λ n : ℕ,
well_founded.fix nat.lt_wf (λ (x) (ih : Π (y : ℕ), nat.lt y x → Type),
  Π (m : fin x), ih m.1 m.2) n

lemma thing_eq : thing =
  (λ n, (Π m : fin n, thing m.1)) :=
begin
  funext,
  rw [thing],
  dsimp,
  rw [well_founded.fix_eq]
end

instance : ∀ n : ℕ, fintype (thing n)
| 0 := ⟨finset.singleton (begin rw thing_eq, exact λ ⟨m, hm⟩, (nat.not_lt_zero _ hm).elim end),
  λ x, mem_singleton.2 (funext $ λ ⟨m, hm⟩, (nat.not_lt_zero _ hm).elim)⟩
| (n+1) := begin
  haveI : ∀ m : fin (n + 1), fintype (thing m.1) :=
    λ m, have m.1 < n + 1, from m.2, thing.fintype m.1,
  rw thing_eq,
  apply_instance
end

#eval fintype.card (thing 4)

example (n : nat) : thing n = sorry :=
begin
  rw thing_eq, rw thing_eq, rw thing_eq, rw thing_eq, rw thing_eq, rw thing_eq,
  dsimp,
end

import data.int.basic

#print int.nat_abs_ne

#exit
class principal_ideal_domain (α : Type*) extends comm_ring α :=
(principal : ∀ (S : set α) [is_ideal S], ∃ a, S = {x | a ∣ x})

lemma prime_factors (n : ℕ) : ∃ l : list ℕ, (∀ p, p ∈ l → nat.prime p) ∧ l.prod = n :=
begin


end

#exit
class has_group_notation (G : Type) extends has_mul G, has_one G, has_inv G

class group' (G : Type) extends has_group_notation G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)
-- Lean 3.4.1 also uses mul_one : ∀ (a : G), a * 1 = a , but we'll see we can deduce it!
-- Note : this doesn't matter at all :-)

variables {G : Type} [group' G]
namespace group'

lemma mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c :=
λ (a b c : G) (Habac : a * b = a * c), -- got to deduce b = c.
calc b = 1 * b : by rw one_mul
... = (a⁻¹ * a) * b : by rw mul_left_inv
... = a⁻¹ * (a * b) : by rw mul_assoc
... = a⁻¹ * (a * c) : by rw Habac
... = (a⁻¹ * a) * c : by rw mul_assoc
... = 1 * c : by rw mul_left_inv
... = c : by rw one_mul

-- now the main theorem

theorem mul_one : ∀ (a : G), a * 1 = a :=
begin
intro a, -- goal is a * 1 = a
apply mul_left_cancel a⁻¹, -- goal now a⁻¹ * (a * 1) = a⁻¹ * a
exact calc a⁻¹ * (a * 1) = (a⁻¹ * a) * 1 : by rw mul_assoc
... = 1 * 1 : by rw mul_left_inv
... = 1 : by rw one_mul
... = a⁻¹ * a : by rw ← mul_left_inv
end
#print mul_one
#exit
import data.nat.basic
#print nat.nat.find_greatest
def nat.find_greatest (P : ℕ → Prop) [decidable_pred P] : ℕ → ℕ
| 0     := 0
| (n+1) := if h : P (n + 1) then n + 1 else nat.find_greatest n

lemma n (α : Type) (n : ℕ) (Hn : cardinal.mk α = n) :
  ∃ l : list α, l.nodup ∧ l.length = n :=
have fintype α, from classical.choice (cardinal.lt_omega_iff_fintype.1
  (Hn.symm ▸ cardinal.nat_lt_omega _)),
let ⟨l, hl⟩ := quotient.exists_rep (@finset.univ α this).1 in
⟨l, show multiset.nodup ⟦l⟧, from hl.symm ▸ (@finset.univ α this).2,
  begin end⟩

lemma three (α : Type) (Hthree : cardinal.mk α = 3) :
  ∃ a b c : α, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ∀ d : α, d = a ∨ d = b ∨ d = c :=
by simp
ₘ
example (s : finset ℕ) : Type := (↑s : set ℕ)

def thing (n : ℕ) := n.factors.erase_dup.length

#eval thing 217094830932814709123840973089487098175


example : f(g*h) = f(g) * f(h) := sorry

def A : set ℝ := {x | x^2 < 3}
def B : set ℝ := {x | x^2 < 3 ∧ ∃ y : ℤ, x = y}

lemma foo : (1 / 2 : ℝ) ∈ A ∩ B :=
begin
split,
rw [A, set.mem_set_of_eq],

{norm_num},


end

example : (1 / 2 : ℝ)^2 < 3 := by norm_num


import data.zmod

lemma gcd_one_of_unit {n : ℕ+} (u : units (zmod n)) :
nat.gcd (u.val.val) n = 1 :=
begin
let abar := u.val, let bbar := u.inv, -- in zmod n
let a := abar.val, let b := bbar.val, -- in ℕ
have H : (a b) % n = 1 % n,
show (abar.val bbar.val) % n = 1 % n,
rw ←mul_val,
rw u.val_inv,
refl,
let d := nat.gcd a n,
show d = 1,
rw ←nat.dvd_one,
rw ←dvd_mod_iff (gcd_dvd_right a n),
rw ←H,
rw dvd_mod_iff (gcd_dvd_right a n),
apply dvd_mul_of_dvd_left,
exact gcd_dvd_left a n
end

lemma hintq3a : ∀ (a b c : zmod 4), 0 = a^2 + b^2 + c^2 → (2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c) := dec_trivial

lemma zmod.cast_nat_dvd {n : ℕ+} {a b : ℕ} (h : a ∣ n) : (a : zmod n) ∣ b ↔ a ∣ b := sorry


#exit
import data.set.basic tactic.interactive

variables {α : Type*} [ring α] (S T : set α)

instance : has_mul (set α) := ⟨λ S T, {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t}⟩
lemma mul_def : S * T =  {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t} := rfl

instance : has_add (set α) :=  ⟨λ S T, {x | ∃ s ∈ S, ∃ t ∈ T, x = s + t}⟩
lemma add_def : S + T =  {x | ∃ s ∈ S, ∃ t ∈ T, x = s + t} := rfl

instance : has_one (set α) := ⟨{1}⟩

instance : has_zero (set α) := ⟨{0}⟩

instance {α : Type*} [ring α] : semiring (set α) :=
{ one_mul := λ a, set.ext $ by simp,
  mul_one := λ a, set.ext $ by simp,
  add_assoc := λ s t u, set.ext $ λ x, ⟨λ h,begin rcases? h,  end, sorry⟩,



  ..set.has_mul,
  ..set.has_add,
  ..set.has_one,
  ..set.has_zero }


#exit
import data.fintype

example : ∀ (f : fin 2 → fin 2 → fin 2),
  (∀ x y z, f (f x y) z = f x (f y z)) → (∀ x, f x 0 = x) →
  (∀ x, ∃ y, f x y = 0) → (∀ x y, f x y = f y x) := dec_trivial


#exit
import data.vector2

lemma vector.ext {α : Type*} {n : ℕ} : ∀ {v w : vector α n}
  (h : ∀ m : fin n, vector.nth v m = vector.nth w m), v = w :=
λ ⟨v, hv⟩ ⟨w, hw⟩ h, subtype.eq (list.ext_le (by rw [hv, hw])
(λ m hm hn, h ⟨m, hv ▸ hm⟩))

lemma vector.nth_of_fn {α : Type*} {n : ℕ} : ∀ (f : fin n → α),
  vector.nth (vector.of_fn f) = f :=

#print opt_param
inductive nested : Type
| nest : list nested → nested
#print has_inv.inv
open nested
#print nested.rec

#print prefix nested

#print vector.of_fn

def nested.rec_on (C : nested → Sort*) (x : nested)  (h0 : C (nest [])) :
  Π (h : Π (l : list nested), (Π a ∈ l, C a) → C (nest l)), C x :=
nested.cases_on _ x (
begin
  assume l,
  induction l with a l ih,
  { exact λ _, h0 },
  { assume h,
    refine h _ (λ b h, _),
     }
end

)

instance : has_well_founded nested :=
⟨λ a b, nested.rec (λ _, Prop) (λ l, a ∈ l) b,
⟨λ a, acc.intro _ (λ b, nested.cases_on _ a (begin
  assume l hb,
  simp at hb,

end))⟩⟩

def nested_dec_eq : ∀ a b : nested, decidable (a = b)
| (nest []) (nest []) := is_true rfl
| (nest []) (nest (a :: l)) := is_false (mt nest.inj (λ h, list.no_confusion h))
| (nest (a :: l)) (nest []) := is_false (mt nest.inj (λ h, list.no_confusion h))
| (nest (a :: l)) (nest (b :: m)) :=

end

#exit
import data.equiv.basic data.fintype
universes u v w

set_option trace.simplify.rewrite true
lemma thing {α : Type*} (p q : Prop) : (∃ hp : p, q) ↔ p ∧ q :=
begin
  simp,

end
#print exists_prop

#exit
#print equiv.coe_fn_mk
#print has_coe_to_fun
theorem coe_fn_mk {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l : function.left_inverse g f)
(r : function.right_inverse g f) : (equiv.mk f g l r : has_coe_to_fun.F (equiv.mk f g l r)) = f := rfl

example {α : Sort*} {β : Sort*} (f : α ≃ β) (a : ℕ) : (equiv.mk (λ a, ite (a = 5) (4 : ℕ) 5)
  sorry sorry sorry : ℕ → ℕ) = sorry :=
begin
  cases f, simp,
  simp only [coe_fn_mk],

end

#exit
import data.real.basic

lemma silly_function : ∃ f : ℝ → ℝ, ∀ x y a : ℝ, x < y → ∃ z : ℝ, x < z ∧ z < y ∧ f z = a := sorry

#print well_founded.fix
#exit
import logic.function

example (x y : ℕ) (h : x ≠ y) (f : ℕ → ℕ) (h₂ : function.injective f) :
  f x ≠ f y := mt (@h₂ x y) h

lemma em_of_iff_assoc : (∀ p q r : Prop, ((p ↔ q) ↔ r) ↔ (p ↔ (q ↔ r))) → ∀ p, p ∨ ¬p :=
λ h p, ((h (p ∨ ¬p) false false).1
⟨λ h, h.1 (or.inr (λ hp, h.1 (or.inl hp))), λ h, h.elim⟩).2 iff.rfl

#print axioms em_of_iff_assoc

#exit
import data.fintype algebra.big_operators linear_algebra.linear_map_module
#print finset.smul

instance {α : Type*} [monoid α] [fintype α] : fintype (units α) :=
fintype.of_equiv {a : α // ∃ }

#exit
import data.nat.prime
import data.nat.modeq
import data.int.modeq
import algebra.group_power

namespace nat

definition quadratic_res (a n: ℕ) := ∃ x: ℕ, a ≡ x^2 [MOD n]

local attribute [instance] classical.prop_decidable

noncomputable definition legendre_sym (a: ℕ) (p:ℕ) : ℤ :=
if quadratic_res a p ∧ ¬ p ∣ a then 1 else
if ¬ quadratic_res a p then -1
else 0

theorem law_of_quadratic_reciprocity (p q : ℕ)(H1: prime p ∧ ¬ p=2)(H2: prime q ∧ ¬ q=2) :
(legendre_sym p q)*(legendre_sym q p) =(-1)^(((p-1)/2)*((q-1)/2)) := sorry

theorem euler_criterion (p : ℕ) (a: ℕ) (hp : prime p ∧ ¬ p=2) (ha : ¬ p ∣ a) :
  a^((p - 1) / 2) ≡ legendre_sym a p [MOD p] := sorry

#exit

def phi (n : nat) := ((finset.range n).filter (nat.coprime n)).card

local notation φ: = phi

lemma phi_n (n : ℕ) : phi n = fintype.card (units (Zmod n)) := sorry


lemma phi_p (p : ℕ) (hp: nat.prime p) : phi p = p-1 :=

calc phi p = p-1


#exit
import data.nat.modeq data.nat.prime data.finset data.complex.basic

#print mul_le_mul_left

definition quadratic_res (a n : ℕ) : Prop := ∃ x : ℕ, a ≡ x^2 [MOD n]

instance : decidable_rel quadratic_res :=
λ a n, if hn : n = 0 then decidable_of_iff (∃ x ∈ finset.range a, a = x^2)
⟨λ ⟨x, _, hx⟩, ⟨x, by rw hx⟩, λ ⟨x, hx⟩, ⟨x, finset.mem_range.2 begin end, begin end⟩⟩
else decidable_of_iff (∃ x ∈ finset.range n, a ≡ x^2 [MOD n])
⟨λ ⟨x, _, hx⟩, ⟨x, hx⟩, λ ⟨x, hx⟩, ⟨x % n, finset.mem_range.2 (begin end), sorry⟩ ⟩


-- definition legendre_sym (a : ℤ) (p : ℕ) :=
-- if quadratic_res a p ∧ ¬ p ∣ a then 1 else
-- if ¬ quadratic_res a p then -1
-- else 0

#exit
import algebra.group_power data.finset data.nat.gcd data.nat.prime

def phi (n : nat) := ((finset.range n).filter n.coprime).card

def phi2 (n : nat) := (n.factors.map nat.pred).prod

#eval phi 1000
#eval phi2 1000

def thing (m n : ℤ) (h : n * n < n * m) : n ^ 2 < n * m := (pow_two n).symm ▸ h

example : 2 + 3 = 5 := add_comm 0 5 ▸ rfl

lemma two_add_three2 : 2 + 3 = 5 := rfl
#exit
import data.int.basic

example (a b : ℤ) : (-3 : ℤ).nat_abs / (-5 : ℤ).nat_abs
  ≠ ((-3 : ℤ) / (- 5 : ℤ)).nat_abs :=
dec_trivial

#print tactic.interactive.induction

set_option trace.simplify.rewrite true
lemma h (α β γ : Type) (f : α → β) (g : β → α) (H : ∀ b : β, f (g b) = b)
  (j : γ → option β) (x : γ) :
  (do y ← (j x), return (f (g y))) = j x :=
by simp [H]

#print h

#exit
import analysis.real

theorem infinite_cover {a b : ℝ} {c : set (set ℝ)} (n : ℕ) :
∃ k : ℕ, 1 ≤ k ≤ n ∧ ∀ c' ⊆ c, {r : ℝ | a+(k-1)*(a+b)/n ≤ r ∧
r ≤ a+k*(a+b)/n} ⊆ ⋃₀ c' → ¬ set.finite c' := sorry

example : ∃! x, x = 2 := ⟨2, rfl, λ y, id⟩
#print exists_unique
#exit

#print array



def f : ℕ → ℕ → ℕ → ℕ → Prop

notation a `≡` b := f a b

set_option pp.implicit true
lemma h : ¬ (2 ∣ 5) := dec_trivial
#print nat.decidable_dvd

example : ¬ (2 | 5) := dec_trivial
open vector_space
variables {α β γ : Type}
  [field α] [vector_space α β] [vector_space α γ]

inductive T : Type
| mk : (ℕ → T) → T

#print T

#exit
import tactic.finish

variables (p q : Prop) (hp : p) (hq : q)

lemma easy : p ↔ p := iff.rfl

theorem not_a_constructivist : (¬(p ∨ q)) ↔ ((¬ p) ∧ (¬ q)) :=
  by finish

#print not_a_constructivist
#exit
import logic.function
open function

def f : (thunk ℕ) → ℕ  := λ _, 0

def g : ℕ → ℕ := λ _, 0

#print thunk

#eval f ((99 : ℕ) ^ 99 ^ 99)

#eval g (99 ^ 99 ^ 99 ^ 99 ^ 99)

#check Σ α : Type, set α

structure g :=
(α : Type)
(f : α → bool)

#print tactic.exact

def gafd (p q : Prop) [decidable p] [decidable q] :
  decidable (p → q) := by apply_instance
#print forall_prop_decidable


def h {α : Sort*} (f : α → α → ℕ) : ¬ surjective f :=
λ h, let ⟨a, ha⟩ := h (λ a, nat.succ (f a a)) in begin
  have : f a a = nat.succ (f a a) := congr_fun ha _,
  exact nat.succ_ne_self _ this.symm,

end
#print h


#exit
import data.multiset

def value_aux' (N_min : multiset ℕ → ℕ) : multiset ℕ → multiset ℕ → ℕ
| C L := N_min (multiset.pmap
  (λ a (h : a ∈ C),
    have multiset.card (C.erase a) < multiset.card C,
      from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
    a - 2 + int.nat_abs (2 - value_aux' (C.erase a) L))
    C (λ _,id) + multiset.pmap
  (λ a (h : a ∈ L),
    have multiset.card (L.erase a) < multiset.card L,
      from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
    a - 4 +int.nat_abs (4 - value_aux' C (L.erase a)))
    L (λ _,id))
using_well_founded {rel_tac := λ _ _,
  `[exact ⟨_, measure_wf (λ CL, multiset.card CL.fst + multiset.card CL.snd)⟩]}

set_option pp.proofs true
#print value_aux'._main._pack
#exit
example (C : multiset ℕ) : decidable (∃ a : ℕ, a ≥ 4 ∧ a ∈ C) :=
suffices this : decidable (∃ a ∈ C, a ≥ 4),
by { resetI, apply @decidable_of_iff _ _ _ this, apply exists_congr, intro, tauto },
by { apply_instance }

set_option pp.implicit true
instance decidable_exists_multiset {α : Type*} (s : multiset α) (p : α → Prop) [decidable_pred p] :
  decidable (∃ x ∈ s, p x) :=
quotient.rec_on s list.decidable_exists_mem (λ a b h, subsingleton.elim _ _)

example (C : multiset ℕ) : decidable (∃ a : ℕ, a ≥ 4 ∧ a ∈ C) :=
decidable_of_iff (∃ a ∈ quotient.out C, a ≥ 4) (⟨λ ⟨x, hx₁, hx₂⟩, ⟨x, hx₂, begin
  rw ← quotient.out_eq C,
  exact hx₁,
end⟩, λ ⟨x, hx₁, hx₂⟩, ⟨x, begin
  rw ← quotient.out_eq C at hx₂,
  exact ⟨ hx₂, hx₁⟩
end⟩⟩)

#exit
import data.num.basic import tactic.basic data.num.lemmas data.list.basic data.complex.basic
open tactic

namespace ring_tac
open tactic

-- We start by modelling polynomials as lists of integers. Note that znum
-- is basically the same as int, but optimised for computations.

-- The list [a0,a1,...,an] represents a0 + a1*x + a2*x^2 + ... +an*x^n

def poly := list znum

-- We now make basic definitions and prove basic lemmas about addition of polynomials,
-- multiplication of a polynomial by a scalar, and multiplication of polynomials.

def poly.add : poly → poly → poly
| [] g := g
| f [] := f
| (a :: f') (b :: g') := (a + b) :: poly.add f' g'

@[simp] lemma poly.zero_add (p : poly) : poly.add [] p = p := by cases p; refl

def poly.smul : znum → poly → poly
| _ [] := []
| z (a :: f') := (z * a) :: poly.smul z f'

def poly.mul : poly → poly → poly
| [] _ := []
| (a :: f') g := poly.add (poly.smul a g) (0 :: poly.mul f' g)

def poly.const : znum → poly := λ z, [z]

def poly.X : poly := [0,1]

-- One problem with our implementation is that the lists [1,2,3] and [1,2,3,0] are different
-- list, but represent the same polynomial. So we define an "is_equal" predicate.

def poly.is_eq_aux : list znum -> list znum -> bool
| [] [] := tt
| [] (h₂ :: t₂) := if (h₂ = 0) then poly.is_eq_aux [] t₂ else ff
| (h₁ :: t₁) [] := if (h₁ = 0) then poly.is_eq_aux t₁ [] else ff
| (h₁ :: t₁) (h₂ :: t₂) := if (h₁ = h₂) then poly.is_eq_aux t₁ t₂ else ff

def poly.is_eq : poly → poly → bool := poly.is_eq_aux

-- evaluation of a polynomial at some element of a commutative ring.
def poly.eval {α} [comm_ring α] (X : α) : poly → α
| [] := 0
| (n::l) := n + X * poly.eval l

-- Lemmas saying that evaluation plays well with addition, multiplication, polynomial equality etc

@[simp] lemma poly.eval_zero {α} [comm_ring α] (X : α) : poly.eval X [] = 0 := rfl

@[simp] theorem poly.eval_add {α} [comm_ring α] (X : α) : ∀ p₁ p₂ : poly,
  (p₁.add p₂).eval X = p₁.eval X + p₂.eval X :=
begin
  intro p₁,
  induction p₁ with h₁ t₁ H,
    -- base case
    intros,simp [poly.eval],
  -- inductive step
  intro p₂,
  cases p₂ with h₂ t₂,
    simp [poly.add],
  unfold poly.eval poly.add,
  rw (H t₂),
  simp [mul_add]
end

@[simp] lemma poly.eval_mul_zero {α} [comm_ring α] (f : poly) (X : α) :
  poly.eval X (poly.mul f []) = 0 :=
begin
  induction f with h t H,
    refl,
  unfold poly.mul poly.smul poly.add poly.mul poly.eval,
  rw H,simp
end

@[simp] lemma poly.eval_smul {α} [comm_ring α] (X : α) (z : znum) (f : poly) :
  poly.eval X (poly.smul z f) = z * poly.eval X f :=
begin
  induction f with h t H, simp [poly.smul,poly.eval,mul_zero],
  unfold poly.smul poly.eval,
  rw H,
  simp [mul_add,znum.cast_mul,mul_assoc,mul_comm]
end

@[simp] theorem poly.eval_mul {α} [comm_ring α] (X : α) : ∀ p₁ p₂ : poly,
  (p₁.mul p₂).eval X = p₁.eval X * p₂.eval X :=
begin
  intro p₁,induction p₁ with h₁ t₁ H,
    simp [poly.mul],
  intro p₂,
  unfold poly.mul,
  rw poly.eval_add,
  unfold poly.eval,
  rw [H p₂,znum.cast_zero,zero_add,add_mul,poly.eval_smul,mul_assoc]
end

@[simp] theorem poly.eval_const {α} [comm_ring α] (X : α) : ∀ n : znum,
  (poly.const n).eval X = n :=
begin
  intro n,
  unfold poly.const poly.eval,simp
end

@[simp] theorem poly.eval_X {α} [comm_ring α] (X : α) : poly.X.eval X = X :=
begin
  unfold poly.X poly.eval,simp
end

-- Different list representing the same polynomials evaluate to the same thing
theorem poly.eval_is_eq {α} [comm_ring α] (X : α) {p₁ p₂ : poly} :
  poly.is_eq p₁ p₂ → p₁.eval X = p₂.eval X :=
begin
  revert p₂,
  induction p₁ with h₁ t₁ H₁,
  { intros p₂ H,
    induction p₂ with h₁ t₁ H₂,refl,
    unfold poly.eval,
    unfold poly.is_eq poly.is_eq_aux at H,
    split_ifs at H,swap,cases H,
    rw [h,←H₂ H],
    simp },
  { intros p₂ H,
    induction p₂ with h₂ t₂ H₂,
    { unfold poly.eval,
      unfold poly.is_eq poly.is_eq_aux at H,
      split_ifs at H,swap,cases H,
      rw [h,H₁ H],
      simp },
    { unfold poly.eval,
      unfold poly.is_eq poly.is_eq_aux at H,
      split_ifs at H,swap,cases H,
      unfold poly.is_eq at H₂,
      rw [h,H₁ H] } }

end

-- That's the end of the poly interface. We now prepare for the reflection.

-- First an abstract version of polynomials (where equality is harder to test, and we won't
-- need to test it). We'll construct a term of this type from (x+1)*(x+1)*(x+1)

-- fancy attribute because we will be using reflection in meta-land
@[derive has_reflect]
inductive ring_expr : Type
| add : ring_expr → ring_expr → ring_expr
| mul : ring_expr → ring_expr → ring_expr
| const : znum → ring_expr
| X : ring_expr
-- Now a "reflection" of this abstract type which the VM can play with.
meta def reflect_expr (X : expr) : expr → option ring_expr
| `(%%e₁ + %%e₂) := do
  p₁ ← reflect_expr e₁,
  p₂ ← reflect_expr e₂,
  return (ring_expr.add p₁ p₂)
| `(%%e₁ * %%e₂) := do
  p₁ ← reflect_expr e₁,
  p₂ ← reflect_expr e₂,
  return (ring_expr.mul p₁ p₂)
| e := if e = X then return ring_expr.X else
  do n ← expr.to_int e,
    return (ring_expr.const (znum.of_int' n))

-- turning the abstract poly into a concrete list of coefficients.
def to_poly : ring_expr → poly
| (ring_expr.add e₁ e₂) := (to_poly e₁).add (to_poly e₂)
| (ring_expr.mul e₁ e₂) := (to_poly e₁).mul (to_poly e₂)
| (ring_expr.const z) := poly.const z
| ring_expr.X := poly.X

-- evaluating the abstract poly
def ring_expr.eval {α} [comm_ring α] (X : α) : ring_expr → α
| (ring_expr.add e₁ e₂) := e₁.eval + e₂.eval
| (ring_expr.mul e₁ e₂) := e₁.eval * e₂.eval
| (ring_expr.const z) := z
| ring_expr.X := X

-- evaluating the abstract and the concrete polynomial gives the same answer
theorem to_poly_eval {α} [comm_ring α] (X : α) (e) : (to_poly e).eval X = e.eval X :=
by induction e; simp [to_poly, ring_expr.eval, *]

-- The big theorem! If the concrete polys are equal then the abstract ones evaluate
-- to the same value.
theorem main_thm {α} [comm_ring α] (X : α) (e₁ e₂) {x₁ x₂}
  (H : poly.is_eq (to_poly e₁) (to_poly e₂)) (R1 : e₁.eval X = x₁) (R2 : e₂.eval X = x₂) : x₁ = x₂ :=
by rw [← R1, ← R2, ← to_poly_eval,poly.eval_is_eq X H, to_poly_eval]

-- Now here's the tactic! It takes as input the unknown but concrete variable x
-- and an expression f(x)=g(x),
-- creates abstract polys f(X) and g(X), proves they're equal using rfl,
-- and then applies the main theorem to deduce f(x)=g(x).

meta def ring_tac (X : pexpr) : tactic unit := do
  X ← to_expr X,
  `(%%x₁ = %%x₂) ← target,
  r₁ ← reflect_expr X x₁,
  r₂ ← reflect_expr X x₂,
  let e₁ : expr := reflect r₁,
  let e₂ : expr := reflect r₂,
  `[refine main_thm %%X %%e₁ %%e₂ rfl _ _],
  all_goals `[simp only [ring_expr.eval,
    znum.cast_pos, znum.cast_neg, znum.cast_zero',
    pos_num.cast_bit0, pos_num.cast_bit1,
    pos_num.cast_one']]

example (x : ℤ) : (x + 1) * (x + 1) = x*x+2*x+1 := by do ring_tac ```(x)

example (x : ℤ) : (x + 1) * (x + 1) * (x + 1) = x*x*x+3*x*x+3*x+1 := by do ring_tac ```(x)

example (x : ℤ) : (x + 1) + ((-1)*x + 1) = 2 := by do ring_tac ```(x)

end ring_tac

def poly := list znum

def poly.add : poly → poly → poly
| [] g := g
| f [] := f
| (a :: f') (b :: g') := (a + b) :: poly.add f' g'

def poly.eval {α} [comm_ring α] (X : α) : poly → α
| [] := 0
| (n::l) := n + X * poly.eval l

#exit
open expr tactic classical


section logical_equivalences
local attribute [instance] prop_decidable
variables {a b : Prop}
theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
iff.intro classical.by_contradiction not_not_intro
theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
iff.intro
(λ h, if ha : a then or.inr (h ha) else or.inl ha)
(λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))
theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)
theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
if ha : a then
or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
else
or.inl ha
theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
iff.intro not_or_not_of_not_and not_and_of_not_or_not
theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
assume h1, or.elim h1 (assume ha, h^.left ha) (assume hb, h^.right hb)
theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
iff.intro not_and_not_of_not_or not_or_of_not_and_not
end logical_equivalences

meta def normalize_hyp (lemmas : list expr) (hyp : expr) : tactic unit :=
do try (simp_at hyp lemmas)

meta def normalize_hyps : tactic unit :=
do hyps ← local_context,
lemmas ← monad.mapm mk_const [``iff_iff_implies_and_implies,
``implies_iff_not_or, ``not_and_iff, ``not_or_iff, ``not_not_iff,
``not_true_iff, ``not_false_iff],
monad.for' hyps (normalize_hyp lemmas)

#exit
def bind_option {X : Type} {Y : Type} :
  option X → (X → option Y) → option Y
| option.none f := @option.none Y
| (option.some x) f := f x

#print option.bind

lemma pierce_em : (∀ p q : Prop, ((p → q) → p) → p) ↔ (∀ p, p ∨ ¬p) :=
⟨λ pierce p, pierce (p ∨ ¬p) (¬p) (λ h, or.inr (λ hp, h (or.inl hp) hp)),
λ em p q, (em p).elim (λ hp _, hp)
  (λ h h₁, h₁ $ (em q).elim (λ hq _, hq) (λ h₂ hp, (h hp).elim))⟩

#print axioms pierce_em

lemma double_neg_em : (∀ p, ¬¬p → p) ↔ (∀ p, p ∨ ¬p) :=
⟨λ dneg p, dneg () (λ h, h (or.inr (h ∘ or.inl))),
λ em p hneg, (em p).elim id (λ h, (hneg h).elim)⟩

#print axioms double_neg_em

lemma demorgan_em : (∀ p q, ¬ (¬p ∧ ¬q) → p ∨ q) ↔ (∀ p, p ∨ ¬p) :=
⟨λ h p, h p (¬p) (λ h, h.2 h.1),
λ em p q h, (em p).elim or.inl $ λ not_p, (em q).elim or.inr
  (λ not_q, (h ⟨not_p, not_q⟩).elim)⟩

#print axioms demorgan_em

lemma implies_to_or_em : (∀ p q, (p → q) → (¬p ∨ q)) ↔ (∀ p, p ∨ ¬p) :=
⟨λ h p, or.symm $ h p p id,
λ em p q hpq, (em p).elim (or.inr ∘ hpq) or.inl⟩

#print axioms implies_to_or_em

#exit
import logic.function data.equiv.basic
open function
universe u
axiom exists_inv_of_bijection {α β : Sort*} {f : α → β}
  (hf : bijective f) : ∃ g : β → α, left_inverse f g ∧ right_inverse f g

axiom em2 (p : Prop) : p ∨ ¬p

lemma choice2 {α : Sort*} : nonempty (nonempty α → α) :=
(em2 (nonempty α)).elim
(λ ⟨a⟩, ⟨λ _, a⟩) (λ h, ⟨false.elim ∘ h⟩)

lemma choice3 : nonempty (Π {α : Sort u}, nonempty α → α) :=
(em2 (nonempty (Π {α : Sort u}, nonempty α → α))).elim id
(λ h, begin

end)


lemma choice_equiv :
  (∀ {α : Sort*}, nonempty (nonempty α → α)) → (nonempty)

lemma exists_inv_of_bijection {α β : Sort*} {f : α → β}
  (hf : bijective f) : ∃ g : β → α, left_inverse f g ∧ right_inverse f g :=
have hchoice : ∀ b : β, nonempty (nonempty {a : α // f a = b} → {a : α // f a = b}) :=
  λ b, choice2,
let choice : Π b : β, nonempty {a : α // f a = b} → {a : α // f a = b} :=
λ b, begin end in

let f : Π b : β, {a : α // f a = b} := λ b, begin end,
begin
  cases hf,


end

example {α : Sort*} : nonempty (nonempty α → α) :=
begin

end

lemma em2 {p : Prop} : p ∨ ¬p :=
let U : Prop → Prop := λ q, q = true ∨ p in
let V : Prop → Prop := λ q, q = false ∨ p in

have u : subtype U := ⟨true, or.inl rfl⟩,
have v : subtype V := ⟨false, or.inl rfl⟩,
have not_uv_or_p : u.1 ≠ v.1 ∨ p :=
  u.2.elim (v.2.elim (λ h₁ h₂, h₁.symm ▸ h₂.symm ▸ or.inl (λ htf, htf ▸ ⟨⟩))
  (λ hp _, or.inr hp)) or.inr,
have p_implies_uv : p → u.1 = v.1 := λ hp,
have U = V := funext (assume x : Prop,
  have hl : (x = true ∨ p) → (x = false ∨ p), from
    assume a, or.inr hp,
  have hr : (x = false ∨ p) → (x = true ∨ p), from
    assume a, or.inr hp,
  show (x = true ∨ p) = (x = false ∨ p), from
    propext (iff.intro hl hr)),
begin

end,
begin

end,
not_uv_or_p.elim
  (λ h, or.inr $ mt p_implies_uv h)
  or.inl




#exit
import tactic.interactive
namespace tactic



run_cmd mk_simp_attr `norm_num2

lemma two_add_three : 2 + 3 = 4 := sorry

attribute [norm_num2] two_add_three

meta def norm_num2 : tactic unit :=
  do simp_all

meta def generalize_proofs (ns : list name) : tactic unit :=
do intros_dep,
   hs ← local_context >>= mfilter is_proof,
   t ← target,
   collect_proofs_in t [] (ns, hs) >> skip

theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
iff.intro classical.by_contradiction not_not_intro

theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
iff.intro
(λ h, if ha : a then or.inr (h ha) else or.inl ha)
(λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))

theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)

theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
if ha : a then
or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
else
or.inl ha

theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
iff.intro not_or_not_of_not_and not_and_of_not_or_not

theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
assume h1, or.elim h1 (assume ha, h^.left ha) (assume hb, h^.right hb)

theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
iff.intro not_and_not_of_not_or not_or_of_not_and_not
end logical_equivalences

meta def normalize_hyp (lemmas : simp_lemmas) (lemmas2 : list name) (hyp : expr) : tactic unit :=
do try (simp_hyp lemmas lemmas2 hyp)

meta def normalize_hyps : tactic unit :=
do hyps ← local_context,
lemmas ← monad.mapm mk_const [``iff_iff_implies_and_implies,
``implies_iff_not_or, ``not_and_iff, ``not_not_iff,
``not_true_iff, ``not_false_iff],
 hyps (normalize_hyp lemmas)


open tactic
universe u

meta def find_same_type : expr → list expr → tactic expr
| e [] := failed
| e (h :: hs) :=
do t ← infer_type h,
(unify e t >> return h) <|> find_same_type e hs

meta def assumption : tactic unit :=
do ctx ← local_context,
t ← target,
h ← tactic.find_same_type t ctx,
exact h
<|> fail "assumption tactic failed"

#print assumption
#print nonempty


#print eq_of_heq

variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc
    log (x * y) = log (exp (log x) * exp(log y))   : by rw [← exp_log_eq hx, ← exp_log_eq hy]
    ...         = log (exp (log x + log y))        : by rw [← exp_add (log x) (log y)]
    ...         = log x + log y                    : by rw [log_exp_eq (log x + log y)]
example : ∀ {α : Sort u} {a a' : α}, a == a' → a = a' :=
λ α a a' h, @heq.rec_on α a (λ β b, begin end) h begin


end

example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do split,
eh ← get_local `h,
mk_const ``and.right >>= apply,
exact eh,
mk_const ``and.left >>= apply,
exact eh

namespace foo
theorem bar : true := trivial
meta def my_tac : tactic unit :=
mk_const ``bar >>= exact

example : true := by my_tac

end foo

#print apply_instance
lemma h : a → b → a ∧ b :=
by do eh1 ← intro `h1,
eh2 ← intro `h2,
applyc ``and.intro,
exact eh1,
exact eh2

#print h

universes u v
open io



#eval put_str "hello " >> put_str "world! " >> put_str (to_string (27 * 39))

#eval (some 2) <|> (some 1)

#print axioms put_str
#check @put_str
#check @get_line

namespace la
structure registers : Type := (x : ℕ) (y : ℕ) (z : ℕ)
def init_reg : registers := registers.mk 0 0 0

def state (S : Type u) (α : Type v) : Type (max u v) := S → α × S

instance (S : Type u) : monad (state S) :=
{ pure := λ α a r, (a, r),
  bind := λ α β sa b s, b (sa s).1 (sa s).2 }

def read {S : Type} : state S S :=
λ s, (s, s)

def write {S : Type} : S → state S unit :=
λ s0 s, ((), s0)

@[reducible] def reg_state := state registers

def read_x : reg_state ℕ :=
do s ← read, return (registers.x s)

def read_y : reg_state ℕ :=
do s ← read, return (registers.y s)

def read_z : reg_state ℕ :=
do s ← read, return (registers.z s)

def write_x (n : ℕ) : reg_state unit :=
do s ← read,
write (registers.mk n (registers.y s) (registers.z s))

def write_y (n : ℕ) : reg_state unit :=
do s ← read,
write(registers.mk (registers.x s) n (registers.z s))

def write_z (n : ℕ) : reg_state unit :=
do s ← read,
write (registers.mk (registers.x s) (registers.y s) n)

def foo : reg_state ℕ :=
do  write_x 5,
    write_y 7,
    x ← read_x,
    write_z (x + 3),
    y ← read_y,
    z ← read_z,
    write_y (y + z),
    y ← read_y,
    return (y ^ 3)

#print foo

end la
#exit

universe u
variables {α β γ δ : Type.{u}} (la : list α)
variables (f : α → list β) (g : α → β → list γ)
(h : α → β → γ → list δ)

inductive option2 (α : Type u) : Type u
| none : option2
| some : α → option2

instance : monad option2 :=
begin
  refine {..},
  refine λ α β, _,

end

#print applicative
#print option.monad
example : list δ :=
do a ← la,
b ← f a,
c ← g a b,


#exit
import data.multiset data.finset order.bounded_lattice

@[derive decidable_eq] structure sle :=
(three_chains : ℕ) -- number of three-chains
(four_loops : ℕ)
(six_loops : ℕ)
(long_chains : multiset ℕ)
(long_chains_are_long : ∀ x ∈ long_chains, x ≥ 4)
(long_loops : multiset ℕ)
(long_loops_are_long : ∀ x ∈ long_loops, x ≥ 8)
(long_loops_are_even : ∀ x ∈ long_loops, 2 ∣ x)

def size (e : sle) : ℕ := sorry

def legal_moves (e : sle) : finset {f : sle // size f < size e} := sorry

def val : sle → with_top ℕ
| e := (legal_moves e).inf
  (λ f, have size f.1 < size e := f.2, (val f.1 : with_top ℕ))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf size⟩]}

def val2 : Π e : sle, legal_moves e ≠ ∅ → ℕ
| e := (legal_moves e).inf
  (λ f, have size f.1 < size e := f.2, (val f.1 : with_top ℕ))

#exit

variables {α β γ δ : Type.{u}} (oa : option α)
variables (f : α → option β) (g : α → β → option γ)
(h : α → β → γ → option δ)

definition test (m : Type → Type) [monad m]
  (α : Type) (s : m α) (β : Type) (t : m β) (γ : Type) (f : α → β → m γ)
  (g : α → β → m γ)
  :=
do a ← s,
b ← t,
return (g a b)

def x : option β :=
do a ← oa,
   b ← f a,
   return b

#print x

example : option δ :=
do a ← oa,
b ← f a,
c ← g a b,
h a b c

#print option.return


@[elab_as_eliminator, elab_strategy] def multiset.strong_induction_on2 {α : Type*} {p : multiset α → Sort*} :
  ∀ (s : multiset α), (∀ s, (∀t < s, p t) → p s) → p s :=
well_founded.fix (measure_wf multiset.card) (λ s ih h, h s (λ t ht, ih t (multiset.card_lt_of_lt ht) h))

#print multiset.strong_induction_on2
definition f (s : multiset ℕ) : ℕ :=
  multiset.strong_induction_on2 s (λ s' H, 0)

#eval f ({1,2,3} : multiset ℕ)

def bar : ℕ → ℕ
| 0     := 0
| (n+1) := list.length
  (list.pmap (λ m (hm : m < n + 1), bar m) [n, n, n]
  (by simp [nat.lt_succ_self]))

set_option pp.proofs true
#print bar._main._pack

def map_rec_on {C : ℕ → Sort*} (f : ℕ → list ℕ) :
  Π (n : ℕ) (h : ∀ m, ∀ k ∈ f m, k < m)
  (c0 : C 0) (ih : (Π n, list ℕ → C (n + 1))), C n
| 0 := λ h c0 ih, c0
| (n+1) := λ h c0 ih, begin have := ih n,
   have := this ((f (n + 1)).map (λ m, map_rec_on,

 end

#eval bar 1

def bar_aux : ℕ → (ℕ → list ℕ) → list ℕ
| 0 _   := []
| (n+1) f := list.repeat 3 $
  list.length (bar_aux n f)

#eval bar_aux 2 (λ n, [n, n, n])

instance subtype.has_decidable_eq (α : Prop) [h : decidable_eq α]
  (p : α → Prop) : decidable_eq (subtype p)
| ⟨_, _⟩ ⟨_, _⟩ := is_true rfl
#print decidable

lemma h (p : Prop) : ¬(p ↔ ¬p) :=
λ h : p ↔ ¬p,
have not_p : ¬p := λ hp : p, h.1 hp hp,
not_p (h.2 not_p)

#print h

def subfunc_to_option {α β: Type} {c: α → Prop} [decidable_pred c]
(f: {x:α // c x} → β) : α → option β :=
λ y: α, if h : c y then some (f (subtype.mk y h)) else none

def option_to_subfunc {α β: Type} (f: α → (option β)) :
  {x : α // option.is_some (f x)} → β | ⟨x, h⟩ := option.get h

theorem inv1 {α β: Type} {c: α → Prop} (f: {x:α // c x} → β) [decidable_pred c] :
∀ y : {x // c x}, option_to_subfunc (@subfunc_to_option α β c _ f) ⟨y.1, sorry⟩ = f y := sorry
#print roption
def option_to_subfunc {α β: Type} (f: α → (option β)) :
  {x : α // f x ≠ none} → β :=
λ y: {x:α // f x ≠ none},
match f y, y.2 with
| some x, hfy := x
| none  , hfy := (hfy rfl).elim
end

def subfunc_to_option {α β: Type} {c: α → Prop} [decidable_pred c]
(f: {x:α // c x} → β) : α → option β :=
λ y: α, if h : c y then some (f (subtype.mk y h)) else none

open lattice
variable {α : Type*}

lemma sup_eq_max [decidable_linear_order α] (a b : with_bot α) : a ⊔ b = max a b :=
le_antisymm (sup_le (le_max_left _ _) (le_max_right _ _)) (max_le le_sup_left le_sup_right)

lemma inf_eq_min [decidable_linear_order α] (a b : with_top α) : a ⊓ b = min a b :=
le_antisymm (le_min inf_le_left inf_le_right) (le_inf (min_le_left _ _) (min_le_right _ _))

#print subtype.eq

#print subtype.eq

lemma well_founded_lt_with_bot {α : Type*} [partial_order α] (h : well_founded ((<) : α → α → Prop)) :
  well_founded ((<) : with_bot α → with_bot α → Prop) :=
have acc_bot : acc ((<) : with_bot α → with_bot α → Prop) ⊥ :=
  acc.intro _ (λ a ha, (not_le_of_gt ha bot_le).elim),
⟨λ a, option.rec_on a acc_bot (λ a, acc.intro _ (λ b, option.rec_on b (λ _, acc_bot)
(λ b, well_founded.induction h b
  (show ∀ b : α, (∀ c, c < b → (c : with_bot α) < a →
      acc ((<) : with_bot α → with_bot α → Prop) c) → (b : with_bot α) < a →
        acc ((<) : with_bot α → with_bot α → Prop) b,
  from λ b ih hba, acc.intro _ (λ c, option.rec_on c (λ _, acc_bot)
    (λ c hc, ih _ (with_bot.some_lt_some.1 hc) (lt_trans hc hba)))))))⟩

lemma well_founded_lt_with_top {α : Type*} [partial_order α] (h : well_founded ((<) : α → α → Prop)) :
  well_founded ((<) : with_top α → with_top α → Prop) :=
have acc_some : ∀ a : α, acc ((<) : with_top α → with_top α → Prop) (some a) :=
λ a, acc.intro _ (well_founded.induction h a
  (show ∀ b, (∀ c, c < b → ∀ d : with_top α, d < some c → acc (<) d) →
    ∀ y : with_top α, y < some b → acc (<) y,
  from λ b ih c, option.rec_on c (λ hc, (not_lt_of_ge lattice.le_top hc).elim)
    (λ c hc, acc.intro _ (ih _ (with_top.some_lt_some.1 hc))))),
⟨λ a, option.rec_on a (acc.intro _ (λ y, option.rec_on y (λ h, (lt_irrefl _ h).elim)
  (λ _ _, acc_some _))) acc_some⟩

#exit

variables {α : Type}

def preimage (f : α → ℕ) (u : ℕ) : set α  := λ x, f x=u

instance [fintype α] [decidable_eq α] (f : α → ℕ) (u : ℕ) : fintype (preimage f u) :=
by unfold preimage; apply_instance

def card_image [fintype α] [decidable_eq α] (f : α → ℕ) (u : ℕ) : ℕ :=
fintype.card (preimage f u)


#exit
variables {α β γ : Type}

-- function f is continuous at point x
axiom continuous_at (x : α) (f : α → β) : Prop

def continuous (f : α → β) : Prop := ∀ x, continuous_at x f

lemma continuous_comp (f : α → β) (g : β → γ) :
  continuous f → continuous g → continuous (g ∘ f) :=
begin
  assume cf cg x,
  unfold continuous at *,
  have := cg (f x)
end
#exit
import data.fintype data.num.lemmas tactic.norm_num data.real.basic
#print prefix subsingleton

@[elab_with_expected_type] lemma subsingleton_thing {α : Type*} [subsingleton α] {P : α → Prop} (a : α)
  (h : P a) (b : α) : P b :=
by rwa subsingleton.elim b a

example {α : Type*} [f₁ : fintype α] (h : fintype.card α = 0) (f₂ : fintype α) :
  @fintype.card α f₂ = 0 :=
@subsingleton_thing (fintype α) _ _ f₁ h _

#print finset.product

lemma e : (2 : ℝ) + 2 = 4 := rfl

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
