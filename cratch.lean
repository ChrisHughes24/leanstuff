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
import data.rat

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
 data.zmod.basic data.polynomial tactic.norm_num data.rat

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
import data.polynomial data.rat tactic.ring
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

#eval (¬ ∃ n : ℤ, n ^ 2 = 2 : bool)
#print nat.gcd._main._pack
example : nat.gcd 4 5 = 1 := rfl

lemma two_not_square : ¬ ∃ n : ℤ, n ^ 2 = 2 := dec_trivial

example : ¬ ∃ n : ℤ, n ^ 2 = 2 :=
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
⟨λ dneg p, dneg _ (λ h, h (or.inr (h ∘ or.inl))),
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
