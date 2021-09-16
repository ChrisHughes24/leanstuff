import tactic
#print thunk
open set
open_locale nnreal

#print nat.strong_induction_on

def SUBMISSION : Prop := Pi (x : ℝ≥0) (P : set ℝ≥0) (hP : is_open P)
  (ih : ∀ x : ℝ≥0, (∀ y, y < x → y ∈ P) → x ∈ P), x ∈ P

lemma nnreal_induction_on (x : ℝ≥0) (P : set ℝ≥0) (hP : is_open P)
  (ih : ∀ x : ℝ≥0, (∀ y, y < x → y ∈ P) → x ∈ P) : x ∈ P :=
classical.by_contradiction $ λ hx,
have hbI : bdd_below Pᶜ, from ⟨0, λ _, by simp⟩,
have hI : Inf Pᶜ ∈ Pᶜ,
  from is_closed.cInf_mem (is_closed_compl_iff.mpr hP) ⟨x, hx⟩ hbI,
hI (ih _ (λ y hyI, by_contradiction $ λ hy, not_le_of_gt hyI (cInf_le hbI hy)))

def G : SUBMISSION := @nnreal_induction_on

#print axioms G


lemma nnreal_recursion {α : Type*} [topological_space α]
  (ih : Π x : ℝ≥0, (∀ y, y < x → α) → α) (Hih : count(x : ℝ≥0) : α :=



#exit
import data.nat.prime data.nat.parity tactic
#print nat.even_pow
theorem even_of_prime_succ_pow (a b : ℕ) (ha : a > 1) (hb : b > 1)
  (hp : nat.prime (a^b + 1)) : 2 ∣ a :=
have ¬ even (a ^ b + 1),
  from hp.eq_two_or_odd.elim
    (λ h, begin
      have : 1 < a ^ b, from nat.one_lt_pow _ _ (by linarith) ha,
      linarith
    end)
    (by simp [nat.not_even_iff]),
begin
  rw [nat.even_add, iff_false_intro nat.not_even_one, iff_false, not_not,
    nat.even_pow] at this,
  exact this.1
end


#exit
import category_theory.limits.shapes.pullbacks

open category_theory
open category_theory.limits



example {A B C : Prop} : A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) :=
⟨λ h, h.right.elim (λ hB, or.inl ⟨h.left, hB⟩) (λ hC, or.inr ⟨h.left, hC⟩),
  λ h, h.elim (λ hAB, ⟨hAB.left, or.inl hAB.right⟩) (λ hAC, ⟨hAC.left, or.inr hAC.right⟩)⟩

example {A B C : Prop} : A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C) :=
⟨λ h, h.elim (λ hA, ⟨or.inl hA, or.inl hA⟩) (λ hBC, ⟨or.inr hBC.left, or.inr hBC.right⟩),
 λ h, h.left.elim or.inl (λ hB, h.right.elim or.inl (λ hC, or.inr ⟨hB, hC⟩))⟩

universes v u

variables {C : Type u} [category.{v} C]

def pushout_of_epi {X Y : C} (f : X ⟶ Y) [epi f] :
  is_colimit (pushout_cocone.mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f) :=
pushout_cocone.is_colimit.mk
  _
  _
  _
  (λ s, s.inl)
  (by simp)
  (λ s, @epi.left_cancellation _ _ _ _ f _ _ _ _
    (by simp [s.condition]))
  (by simp { contextual := tt })

theorem epi_of_pushout {X Y : C} (f : X ⟶ Y)
  (is_colim : is_colimit (pushout_cocone.mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f)) : epi f :=
{ left_cancellation := λ Z g h H,
    (is_colim.fac (pushout_cocone.mk _ _ H) (walking_span.left)).symm.trans
      (is_colim.fac (pushout_cocone.mk _ _ H) (walking_span.right))}

#exit
import tactic

def arith_sum : ℕ → ℕ
| 0 := 0
| (nat.succ n) := nat.succ n + arith_sum n

def arith_formula (n : ℕ) : ℕ := n * (n + 1) / 2

theorem arith_eq_aux (n : ℕ) : arith_sum n * 2 = n * (n + 1) :=
begin
  induction n with n ih,
  { refl },
  { rw [arith_sum, add_mul, ih, nat.succ_eq_add_one],
    ring }
end

theorem arith_eq (n : ℕ) : arith_formula n = arith_sum n :=
nat.div_eq_of_eq_mul_left (by norm_num) (arith_eq_aux n).symm

#exit
import category_theory.limits.shapes.pullbacks

open category_theory
open category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]

#print limit.lift
#print walking_cospan
#print pullback_cone
#print cone
def right_is_pullback {X Y Z U V : C} (f : X ⟶ Y) (g : X ⟶ Z) (u₁ : Y ⟶ U) (u₂ : Z ⟶ U)
  (v₁ : Y ⟶ V) (v₂ : Z ⟶ V) (hu : f ≫ u₁ = g ≫ u₂) (hv : f ≫ v₁ = g ≫ v₂)
  (is_pullback : is_limit (pullback_cone.mk _ _ hu))
  (is_pushout : is_colimit (pushout_cocone.mk _ _ hv)) :
  is_limit (pullback_cone.mk _ _ hv) :=
let h : V ⟶ U := is_pushout.desc (pushout_cocone.mk u₁ u₂ hu) in
have Hh₁ : v₁ ≫ h = u₁, from is_pushout.fac (pushout_cocone.mk u₁ u₂ hu) walking_span.left,
have Hh₂ : v₂ ≫ h = u₂, from is_pushout.fac (pushout_cocone.mk u₁ u₂ hu) walking_span.right,
let S : pullback_cone v₁ v₂ → pullback_cone u₁ u₂ :=
  λ s, pullback_cone.mk s.fst s.snd
    (by rw [← Hh₁, ← Hh₂, ← category.assoc, ← category.assoc, s.condition]) in
pullback_cone.is_limit.mk _ _ _
  (λ s, is_pullback.lift (S s))
  (λ s, is_pullback.fac (S s) walking_cospan.left)
  (λ s, is_pullback.fac (S s) walking_cospan.right)
  begin
    assume s (m : s.X ⟶ X) h₁ h₂,
    refine is_pullback.uniq (S s) m (λ j, _),
    cases j,
    { dsimp,
      simp [← h₁] },
    { cases j; dsimp; simp * }
  end

#exit
import algebra.group

class my_group (G : Type*) extends semigroup G :=
( middle : ∀ (x : G), ∃! (y : G), x * y * x = x)

variables {G : Type*} [my_group G] --[nonempty G]

noncomputable theory

namespace my_group

instance A : has_inv G := ⟨λ x, classical.some (my_group.middle x)⟩

lemma mul_inv_mul (x : G) : x * x⁻¹ * x = x :=
(classical.some_spec (my_group.middle x)).1

lemma inv_unique {x y : G} (h : x * y * x = x) : y = x⁻¹ :=
(classical.some_spec (my_group.middle x)).2 _ h

variable [nonempty G]

open_locale classical


variables (x y z : G)

def one := x * x⁻¹

lemma one_inv : (one x)⁻¹ = one x :=
(inv_unique begin
  delta one,
  assoc_rw [mul_inv_mul, mul_inv_mul],
end).symm

example : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
eq.symm (inv_unique _)

example : x * x⁻¹ * y * y⁻¹ = (y⁻¹ * y)⁻¹ :=
inv_unique _

lemma one_eq_one : one x = (y * y⁻¹) :=
begin


end

@[simp] lemma inv_inv : x⁻¹⁻¹ = x :=
(inv_unique (inv_unique (by assoc_rw [mul_inv_mul, mul_inv_mul]))).symm

lemma inv_mul_inv : x⁻¹ * x * x⁻¹ = x⁻¹ :=
calc x⁻¹ * x * x⁻¹ = x⁻¹ * x⁻¹⁻¹ * x⁻¹ : by rw inv_inv
... = x⁻¹ : mul_inv_mul (x⁻¹)

lemma one_eq_one : one (x⁻¹) = one x :=
begin
  rw [← one_inv x, one, one],
  refine (inv_unique _),
  simp only [mul_assoc],
  refine congr_arg _ _,
  refine (inv_unique _),
  assoc_rw [mul_inv_mul],
  rw inv_inv,

end


example : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
(inv_unique _).symm

example : x⁻¹ * 1 = x⁻¹ :=
inv_unique _

example : y⁻¹ * x⁻¹ * x = y⁻¹ :=
inv_unique _


lemma mul_one_mul_arbitrary {x : G} : x * 1 * classical.arbitrary G = x * classical.arbitrary G :=


lemma mul_one (x : G) : x * x⁻¹ = 1 :=


end my_group

#exit
import data.real.basic

/- We first define uniform convergence -/
def unif_convergence (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) :=
∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ, abs (f n x - g x) < ε

/- Use the notation f → g to denote that the sequence fₙ converges uniformly to g
    You can type ⟶ by writing \hom -/
notation f `⟶` g := unif_convergence f g

/- We also define the notion of the limit of a function ℝ → ℝ at a point -/
def fun_limit (f : ℝ → ℝ) (a l) :=
∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x ≠ a → abs (x - a) < δ → abs (f x - l) < ε

/- And the notion of the limit of a sequence -/
def seq_limit (f : ℕ → ℝ) (l) :=
∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, abs (f n - l) < ε

/- If fₙ is a sequence of functions which converge uniformly to a function g
    and if lim_{x → a} fₙ(x) exists for each n then lim_{x → a} g(x) exists
    and is equal to lim_{n → ∞} lim_{x → a} fₙ(x). -/
theorem limits_commute (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (l : ℕ → ℝ) (a : ℝ) :
    (f ⟶ g) → (∀ n, fun_limit (f n) a (l n)) → ∃ l', fun_limit g a l' ∧ seq_limit l l' :=
begin
  rw [unif_convergence],
  delta fun_limit seq_limit,
  assume hfg hs,

end


#exit
import data.fintype.basic
import set_theory.ordinal_arithmetic
import order.order_iso_nat

universe u

variable {α : Type u}

--open ordinal

attribute [elab_as_eliminator] well_founded.fix
open_locale classical
noncomputable theory

#print ordinal.omega

noncomputable def nat_embedding [infinite α] (r : α → α → Prop)
  (hrwo : is_well_order α r) : ℕ → α
| n := well_founded.min hrwo.wf
  (finset.univ.image (λ m : fin n, have wf : m.1 < n := m.2, nat_embedding m.1))ᶜ
  (infinite.exists_not_mem_finset
    (finset.univ.image (λ m : fin n, have wf : m.1 < n := m.2, nat_embedding m.1)))

#print rel_embedding.swap
theorem fintype_of_well_order (r : α → α → Prop)
  (hrwo : is_well_order α r) (hrwo' : is_well_order α (λ x y, r y x)) :
  nonempty (fintype α) :=
classical.by_contradiction $ λ h,
have cardinal.omega ≤ (ordinal.type r).card,
  from le_of_not_gt (mt cardinal.lt_omega_iff_fintype.1 h),
have ordinal.omega ≤ ordinal.type r,
  by rwa [← cardinal.ord_omega, cardinal.ord_le],
have f : nonempty (((>) : ℕ → ℕ → Prop) ↪r function.swap r),
  begin
    rw [ordinal.omega, ← ordinal.lift_id (ordinal.type r)] at this,
    rcases (ordinal.lift_type_le.{0 u}.1 this) with ⟨f, hf⟩,
    exact ⟨f.swap⟩,
  end,
rel_embedding.well_founded_iff_no_descending_seq.1 hrwo'.wf f


theorem fintype_of_well_order (r : α → α → Prop)
  (hrwo : is_well_order α r) (hrwo' : is_well_order α (λ x y, r y x)) :
  nonempty (fintype α) :=
classical.by_contradiction $ λ h,
have infin : infinite α, from ⟨h ∘ nonempty.intro⟩,
let a : α := classical.choice (@infinite.nonempty α ⟨h ∘ nonempty.intro⟩) in
let f : ℕ → α := λ n, well_founded.fix (well_founded.min hrwo.wf set.univ ⟨a, trivial⟩)
(well_founded.min _ _)


#exit

/-- The hat color announced by the dwarf with the number `n` upon seeing the colors of the hats in
    front of him: `see i` is the color of the hat of the dwarf with the number `n + i + 1`. -/
noncomputable def announce (n : ℕ) (see : ℕ → α) : α :=
choose_fun (λ m, see (m - n - 1)) n

-- see' :
-- announce (n + 1) (λ n, see (n + 1)) = see 0

/-- Only finitely many dwarves announce an incorrect color. -/
theorem announce_correct_solution (col : ℕ → α) :
  ∃ N : ℕ, ∀ n ≥ N, col n = announce n (λ m, col (m + n + 1)) :=
have ∀ n : ℕ, choose_fun (λ m : ℕ, col (m - n - 1 + n + 1)) = choose_fun col,
  from λ n, choose_fun_eq ⟨n + 1, λ k hk,
    by rw [add_assoc, nat.sub_sub, nat.sub_add_cancel hk]⟩,
begin
  delta announce,
  simp only [this],
  exact choose_fun_spec _
end


#exit
import category_theory.functor
import category_theory.types
import category_theory.monad
import algebra.module
open category_theory monad

@[simps]
def P : Type ⥤ Type :=
{ obj := λ X, set X,
  map := λ X Y, set.image }

variables {R : Type 1} [comm_ring R] {M : Type} [add_comm_group M]

#check module R M

#check Σ (M : Type) [add_comm_group M], by exactI module R M

instance powerset_monad : monad P :=
{ η :=
    { app := λ X x, ({x} : set X),
      naturality' :=
        λ X Y f, (funext (@set.image_singleton _ _ f)).symm },
  μ :=
    { app := @set.sUnion,
      naturality' := begin
        intros X Y f,
        ext,
        simp,
        dsimp [P_obj],
        tauto
      end },
  assoc' := begin
      intro X,
      ext,
      simp,
      dsimp,
      tauto
    end,
  left_unit' := begin
      intro X,
      dsimp,
      ext,
      simp,
    end,
  right_unit' := begin
      intro X,
      dsimp,
      ext,
      simp
    end }

#exit
inductive tm : Type
  | zro : tm
  | scc : tm -> tm
  | pls : tm -> tm -> tm
  | nul : tm
  | cns : tm -> tm -> tm
  | len : tm -> tm
  | idx : tm -> tm -> tm
  | stn : tm -> tm
open tm

inductive nvalue : tm -> Prop
  | nv_zro : nvalue zro
  | nv_scc : Π v1, nvalue v1 -> nvalue (scc v1)
open nvalue

inductive lvalue : tm -> Prop
  | lv_nul : lvalue nul
  | lv_cns : Π v1 v2,
      nvalue v1 -> lvalue v2 -> lvalue (cns v1 v2)

def value (t : tm) := nvalue t ∨ lvalue t

inductive step : tm -> tm -> Prop
notation x  ` ⟶ `:100 y := step x y
  | ST_Scc : ∀ t1 t1',
      (t1 ⟶ t1') →
      scc t1 ⟶ scc t1'
  | ST_PlsZro : ∀ v1,
      nvalue v1 →
      pls zro v1 ⟶ v1
  | ST_PlsScc : ∀ v1 v2,
      nvalue v1 →
      nvalue v2 →
      pls (scc v1) v2 ⟶ scc (pls v1 v2)
  | ST_Pls2 : ∀ v1 t2 t2',
      nvalue v1 →
      (t2 ⟶ t2') →
      pls v1 t2 ⟶ pls v1 t2'
  | ST_Pls1 : ∀ t1 t1' t2,
      (t1 ⟶ t1') →
      pls t1 t2 ⟶ pls t1' t2
  | ST_Cns2 : ∀ v1 t2 t2',
      nvalue v1 →
      (t2 ⟶ t2') →
      cns v1 t2 ⟶ cns v1 t2'
  | ST_Cns1 : ∀ t1 t1' t2,
      (t1 ⟶ t1') →
      cns t1 t2 ⟶ cns t1' t2
  | ST_LenNul :
      len nul ⟶ zro
  | ST_LenCns : ∀ v1 v2,
      nvalue v1 →
      lvalue v2 →
      len (cns v1 v2) ⟶ scc (len v2)
  | ST_Len : ∀ t1 t1',
      (t1 ⟶ t1') →
      len t1 ⟶ len t1'
  | ST_IdxZro : ∀ v1 v2,
      nvalue v1 →
      lvalue v2 →
      idx zro (cns v1 v2) ⟶ v1
  | ST_IdxScc : ∀ v1 v2 v3,
      nvalue v1 →
      nvalue v2 →
      lvalue v3 →
      idx (scc v1) (cns v2 v3) ⟶ idx v1 v3
  | ST_Idx2 : ∀ v1 t2 t2',
      nvalue v1 →
      (t2 ⟶ t2') →
      idx v1 t2 ⟶ idx v1 t2'
  | ST_Idx1 : ∀ t1 t1' t2,
      (t1 ⟶ t1') →
      idx t1 t2 ⟶ idx t1' t2
  | ST_StnNval : ∀ v1,
      nvalue v1 →
      stn v1 ⟶ cns v1 nul
  | ST_Stn : ∀ t1 t1',
      (t1 ⟶ t1') →
      stn t1 ⟶ stn t1'
open step

infix ` ⟶ `:100 := step

def relation (X : Type) := X → X → Prop

def deterministic {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2

inductive ty : Type
  | Nat : ty
  | List : ty
open ty

inductive has_type : tm → ty → Prop
notation `⊢ `:79 t ` :∈ `:80 T := has_type t T
  | T_Zro :
      ⊢ zro :∈ Nat

  | T_Scc : ∀ t1,
      (⊢ t1 :∈ Nat) →
      ⊢ scc t1 :∈ Nat
  | T_Pls : ∀ t1 t2,
      (⊢ t1 :∈ Nat) →
      (⊢ t2 :∈ Nat) →
      ⊢ pls t1 t2 :∈ Nat

  | T_Nul :
      ⊢ nul :∈ List
  | T_Cns : ∀ t1 t2,
      (⊢ t1 :∈ Nat) →
      (⊢ t2 :∈ List) →
      ⊢ cns t1 t2 :∈ List

  | T_Len : ∀ t1,
      (⊢ t1 :∈ List) →
      (⊢ len t1 :∈ Nat)
  | T_Idx : ∀ t1 t2,
      (⊢ t1 :∈ Nat) →
      (⊢ t2 :∈ List) →
      ⊢ idx t1 t2 :∈ Nat
  | T_Stn : ∀ t1,
      (⊢ t1 :∈ Nat) →
      ⊢ stn t1 :∈ List
open has_type

notation `⊢ `:19 t ` :∈ `:20 T := has_type t T

def progress := ∀ t T,
  (⊢ t :∈ T) →
  value t ∨ ∃ t', t ⟶ t'

def preservation := ∀ t t' T,
  (⊢ t :∈ T) →
  t ⟶ t' →
  ⊢ t' :∈ T

inductive multi {X : Type} (R : relation X) : relation X
  | multi_refl : ∀ (x : X), multi x x
  | multi_step : ∀ (x y z : X),
                    R x y →
                    multi y z →
                    multi x z

def multistep := (multi step).
infix ` ⟶* `:100  := (multistep)

def normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'

notation `step_normal_form` := (normal_form step)

def stuck (t : tm) : Prop :=
  step_normal_form t ∧ ¬ value t

def soundness := ∀ t t' T,
  (⊢ t :∈ T) →
  t ⟶* t' →
  ¬ stuck t'


theorem step_deterministic : deterministic step :=
begin
  unfold deterministic,
  assume x y1 y2 h1 h2,
  induction h1; induction h2; simp *,

end

/- Uncomment one of the following two: -/
-- theorem progress_dec : progress := sorry
-- theorem progress_dec : ¬ progress := sorry

/- Uncomment one of the following two: -/
-- theorem preservation_dec : preservation := sorry
-- theorem preservation_dec : ¬ preservation := sorry

/- Uncomment one of the following two: -/
-- lemma soundness_dec : soundness := sorry
-- lemma soundness_dec : ¬ soundness := sorry


#exit
import data.list
import data.stream
import data.nat.basic
import data.nat.fib
import data.nat.parity

open nat

def fib_aux : ℕ → ℕ → ℕ → ℕ
| a b 0 := a
| a b (n + 1) := fib_aux b (a + b) n

def fib2 (n : ℕ) : ℕ := fib_aux 0 1 n

def fib_from (a b : ℕ) : ℕ → ℕ
| 0 := a
| 1 := b
| (n+2) := fib_from n + fib_from (n+1)

lemma fib_from_thing (a b : ℕ) : ∀ n, fib_from b (a + b) n = fib_from a b n.succ
| 0 := rfl
| 1 := rfl
| (n+2) := begin
  rw [fib_from, fib_from_thing, fib_from, fib_from_thing],
end

lemma fib_aux_eq : ∀ a b n : ℕ, fib_aux a b n = fib_from a b n
| a b 0 := rfl
| a b 1 := rfl
| a b (n+2) := begin
  rw [fib_aux, fib_from, fib_aux_eq],
  rw [fib_from_thing, fib_from],
end

lemma fib_from_eq_fib : ∀ n, fib_from 0 1 n = fib n
| 0 := rfl
| 1 := rfl
| (n+2 ) := begin
  rw [fib_from, fib_from_eq_fib, fib_succ_succ, fib_from_eq_fib],
end

theorem fib_eq (n : ℕ) : fib2 n = fib n :=
begin
  rw [fib2, fib_aux_eq, fib_from_eq_fib],
end


theorem fib_fast_correct (n : ℕ) : fib_fast n = fib n :=
begin


end

#exit
import category_theory.functor
import category_theory.types
import category_theory.monad
import data.set.basic

@[simps]
def P : Type ⥤ Type :=
{ obj := λ X, set X,
  map := λ X Y, set.image }

open category_theory monad
#print has_singleton
instance powerset_monad : monad P :=
{ η :=
  { app := λ X, as_hom (has_singleton.singleton : X → set X) },
  μ :=
  { app := λ X, set.sUnion,
    naturality' := begin
      assume X Y f,
      ext,
      dsimp [P_obj, P_map],

    end } }

open category_theory monad

universe u

-- A suggested solution method.
-- You are *not* required to use this.

@[simps]
def contravariant_powerset : (Type u)ᵒᵖ ⥤ Type u :=
{ obj := λ X, set X.unop,
  map := λ X Y f, as_hom (set.preimage f.unop),
  map_id' := λ x, by dsimp; refl,
  map_comp' := λ X Y Z f g, by { dsimp at *, ext1, dsimp at *, ext1, simp at * } }
#print op_op
instance : is_right_adjoint contravariant_powerset :=
{ left := unop_unop (Type u) ⋙ contravariant_powerset.op,
  adj := adjunction.mk_of_unit_counit
    { unit :=
      { app := λ X (x : X), ({S : set X | x ∈ S} : set (set X)),
        naturality' := by { intros X Y f, refl} },
      counit :=
      { app := λ X,
          let f : X.unop ⟶ set (set (opposite.unop X)) :=
            as_hom (λ x : X.unop, ({S : set X.unop | x ∈ S} : set (set X.unop))) in
          begin
            have := f.op,

          end,
        naturality' := begin
          intros X Y f,
          refine has_hom.hom.unop_inj _,
          dsimp at *, refl,
        end },
      left_triangle' := begin
        dsimp at *, simp at *, ext1, dsimp at *, ext1, dsimp at *, simp at *,
        refine has_hom.hom.unop_inj _,
        dsimp at *, refl
      end,
      right_triangle' := by { dsimp at *, simp at *, ext1, dsimp at *, ext1, dsimp at *, refl} } }

@[simps]
def PP : Type u ⥤ Type u :=
{ obj := λ X, set (set X),
  map := λ X Y f, set.preimage (set.preimage f) }

def PP1 : Type u ⥤ Type u :=
unop_unop (Type u) ⋙ contravariant_powerset.op ⋙ contravariant_powerset

lemma PP_eq_PP1 : PP.{u} = PP1 := rfl

instance double_powerset_monad : category_theory.monad PP :=
by rw [PP_eq_PP1]; exact adjunction.monad _

#exit
import data.fintype.basic

universe u

variable {α : Type u}

local attribute [elab_as_eliminator] well_founded.fix

theorem fintype_of_well_order (r : α → α → Prop)
  (hrwo : is_well_order α r) (hrwo' : is_well_order α (λ x y, r y x)) :
  nonempty (fintype α) :=
classical.by_contradiction $ λ h,
have ∀ a : α, ¬ nonempty (fintype {b // r a b}),
  from sorry,


def SUBMISSION : Prop :=
∀ {G : Type} [group G] {a b : G} (h : by exactI a * b * a * b^2 = 1),
  by exactI a * b = b * a

set_option profiler true

lemma F {G : Type} [group G] {a b : G} (h : a * b * a * b ^ 2 = 1) :
  a * b = b * a :=
calc a * b = (b⁻¹ * a⁻¹ * (a * b * a * b^2)
  * a * b * b * (a * b * a * b^2)⁻¹ * b⁻¹) * b * a : by group
... = b * a : by rw h; group

lemma G {G : Type} [group G] {a b : G} (n : ℕ) (h : (a * b) ^ n * b = 1) :
  a * b = b * a :=
calc a * b = a * b^2 * ((a * b) ^ n * b) * b^ (-2 : ℤ) * a⁻¹ * b *
    ((a * b) ^ n * b)⁻¹ * b⁻¹ * b * a :
  begin
    simp only [mul_assoc, pow_two, mul_inv_cancel_left, mul_inv_rev, gpow_neg,
      pow_bit0, gpow_bit0, gpow_one, pow_one],
    rw [← mul_assoc b⁻¹ a⁻¹, ← mul_assoc _ ((a * b) ^n)⁻¹, ← mul_inv_rev,
      ← mul_inv_rev, ← pow_succ', pow_succ],
    simp [mul_assoc]
  end
... = _ : by rw h; group


#exit
import tactic

variables {G : Type} [group G]

def fib_thing (b₁ b₀ : G) : ℕ → G
| 0     := b₁
| 1     := b₁ * b₀
| (n+2) := fib_thing (n + 1) * fib_thing n

lemma a_mul_fib_thing {a b₁ b₀ : G} (hab₁ : a * b₁ = b₁ * b₀ * a)
  (hab₀ : a * b₀ = b₁ * a) : ∀ n : ℕ,
  a * fib_thing b₁ b₀ n = fib_thing b₁ b₀ (n + 1) * a
| 0 := by simp [fib_thing, hab₁]
| 1 := begin
  unfold fib_thing,
  rw [← mul_assoc, hab₁, mul_assoc, hab₀, mul_assoc, mul_assoc, mul_assoc],
end
| (n+2) := by rw [fib_thing, ← mul_assoc, a_mul_fib_thing, mul_assoc, a_mul_fib_thing,
    fib_thing, fib_thing, fib_thing, mul_assoc, mul_assoc, mul_assoc]

lemma X (a b₁ b₀ : G) (hab₁ : a * b₁ = b₁ * b₀ * a)
  (hab₀ : a * b₀ = b₁ * a) :
  ∀ (n : ℕ), a^n * b₁ = fib_thing b₁ b₀ n * a ^ n
| 0 := by simp [fib_thing]
| (n+1):= by rw [pow_succ, mul_assoc, X, ← mul_assoc, a_mul_fib_thing hab₁ hab₀,
  mul_assoc]

lemma Y (a b₀ bₙ₁ : G) (hab₁ : a⁻¹ * bₙ₁ = bₙ₁⁻¹ * b₀ * a)
  (hab₀ : a⁻¹ * b₀ = bₙ₁ * a) :

#exit
import linear_algebra.tensor_algebra
import data.real.basic
/--
attempt to unmathlibify
-/

variables (R : Type) [ring R] (M : Type) [add_comm_group M] [module R M]
/-
semimodule.add_comm_monoid_to_add_comm_group :
Π (R : Type u) {M : Type w} [_inst_1 : ring R] [_inst_2 : add_comm_monoid M]
[_inst_3 : semimodule R M], add_comm_group M
-/

def typealias (α : Type) := ℤ

local attribute [irreducible] tensor_algebra

-- def foo : add_comm_group (tensor_algebra ℤ ℤ) := by apply_instance -- tensor_algebra.ring ℤ

-- def bar : add_comm_group (typealias bool) := by unfold typealias; apply_instance

-- def foo' : add_comm_group (tensor_algebra ℤ ℤ) :=
--   semimodule.add_comm_monoid_to_add_comm_group ℤ

-- def bar' : add_comm_group (typealias bool) := by unfold typealias;
--   exact semimodule.add_comm_monoid_to_add_comm_group ℤ
--instance foo'' : ring (tensor_algebra ℤ ℤ) := by apply_instance
#print tactic.dsimp_config
local attribute [irreducible] typealias

local attribute [irreducible] tensor_algebra

instance foo' : ring (tensor_algebra ℤ ℤ) :=
{ ..semimodule.add_comm_monoid_to_add_comm_group (tensor_algebra ℤ ℤ),
  ..(infer_instance : semiring (tensor_algebra ℤ ℤ)) }

instance foo : ring (tensor_algebra ℤ ℤ) := tensor_algebra.ring ℤ

example : derive_handler := by library_search

@[derive ring] def C := int
#print d_array
#print C.ring

set_option pp.implicit true
set_option pp.proofs true

--lemma X : @ring.add_zero _ foo = @ring.add_zero _ foo' := rfl

#print declaration
#print expr

run_cmd tactic.add_decl
  (declaration.thm `X []  `(@ring.add_zero _ foo = @ring.add_zero _ foo')
  (pure `(eq.refl (@ring.add_zero _ foo))))

#print X

 -- works when `tensor_algebra` is not irreducible
-- example : @add_comm_group.add_zero _ foo = @add_comm_group.add_zero _ foo' := rfl

-- works when `typealias` is not irreducible, but *statement* doesn't compile if it is
example : @add_comm_group.add_zero _ bar = @add_comm_group.add_zero _ bar' :=
rfl

#exit

#print list.range

example {G : Type*} [group G] (a b : G) (hab : a * b = b * a⁻¹ * b * a^2) :
  a * a * a * b = sorry :=
have hab' : ∀ g : G, a * (b * g) = b * (a⁻¹ * (b * (a * (a * g)))),
  from λ g, by rw [← mul_assoc, hab]; simp [pow_two, mul_assoc],
begin
  simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left],
  try { rw [hab] <|> rw hab'},
  simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left],
  try { rw [hab] <|> rw hab'},
  simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left],
  try { rw [hab] <|> rw hab'},
  simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left],
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  try { rw [hab] <|> rw hab'},
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },
  rw [hab] <|> rw hab',
  try { simp only [mul_assoc, pow_two, mul_left_inv, mul_right_inv, one_inv,
    mul_inv_cancel_left, inv_mul_cancel_left] },


end

example {G : Type*} [group G] (a b : G) (hab : a * b = b * a⁻¹ * b * a^2) (n : ℕ) :
  a^n * b = ((list.range n).map (λ i, b ^ (2 ^ i) * a⁻¹)).prod * b
   * a ^ (2 ^ (n + 1))

example {G : Type*} [group G] (a b : G) (hab : a * b = b * a⁻¹ * b * a^2) (n : ℕ) :
  a^(n + 1) * b = ((list.range (n+1)).map (λ i, b ^ (2 ^ i) * a⁻¹)).prod * b
   * a ^ (2 ^ (n + 1)) :=
begin
  induction n with n ih,
  { simp [list.range, list.range_core, hab] },
  { rw [pow_succ, mul_assoc, ih, eq_comm, list.range_concat, list.map_append],
    simp, }

end

#exit
notation `C∞` := multiplicative ℤ

open multiplicative

lemma to_add_injective {A : Type*} : function.injective (to_add : A → multiplicative A) :=
λ _ _, id

@[derive group] def Z_half : Type :=
multiplicative (localization.away (2 : ℤ))

def phi : C∞ →* mul_aut Z_half :=
gpowers_hom _
  (show mul_aut Z_half, from
    { to_fun := λ x, of_add (to_add x * 2),
      inv_fun := λ x, of_add (to_add x * localization.away.inv_self 2),
      left_inv := λ _, to_add_injective sorry,
      right_inv :=  λ _, to_add_injective sorry,
      map_mul' := λ _ _, to_add_injective sorry })

@[derive group] def BS : Type := Z_half ⋊[phi] C∞

@[simp] lemma zero_denom : (0 : ℚ).denom = 1 := rfl

def lift {G : Type*} [group G] (a b : G) (hab : a * b * a⁻¹ = b^2) : BS →* G :=
semidirect_product.lift
  _
  (gpowers_hom _ a)
  _


#exit

@[derive decidable_eq] inductive BS : Type
| neg    : ℕ+ → ℤ → BS
| nonneg : ℤ → ℕ → BS

namespace BS

private def one : BS := nonneg 0 0

private def inv : BS → BS
| (neg n i) := nonneg (-i) n
| (nonneg i n) :=
  if hn : 0 < n then neg ⟨n, hn⟩ (-i) else nonneg (-i) 0

private def mul : BS → BS → BS
| (nonneg i₁ n₁) (nonneg i₂ n₂) := nonneg (i₁ + i₂ + i₂.sign * max n₁ i₂.nat_abs) (n₁ + n₂)
| (nonneg i₁ n₁) (neg n₂ i₂)    :=
  if hn : (n₂ : ℕ) ≤ n₁
    then nonneg (i₁ + i₂ + i₂.sign * max (n₁ - n₂) i₂.nat_abs) (n₁ - n₂)
    else neg ⟨n₂ - n₁, nat.sub_pos_of_lt (lt_of_not_ge hn)⟩
      (i₁.sign * max (n₂ - n₁) i₁.nat_abs + i₁ + i₂)
| (neg n₁ i₁) (nonneg i₂ n₂)    :=
  if hn : (n₁ : ℕ) ≤ n₂
    then nonneg _ (n₂ - n₁)
    else _


end BS

#exit
private def mul (a b : B) : B :=
if b.conj +

private def one : BS := ⟨0, 0, 0, dec_trivial⟩

instance : has_one BS := ⟨one⟩

private def inv (a : BS) : BS :=
⟨a.right, -a.middle, a.left, by cases a; simp; tauto⟩

instance : has_inv BS := ⟨inv⟩

private def mul (a b : BS) : BS :=
let x : {x : ℕ × ℕ // a.middle + b.middle = 0 → x.1 = 0 ∨ x.2 = 0} :=
  let m : ℤ := a.right - b.left in
  if h : a.middle + b.middle = 0
    then let k : ℤ := a.left + b.left - a.right - b.right in
      if 0 ≤ k
        then ⟨(k.to_nat, 0), λ _, or.inr rfl⟩
        else ⟨(0, k.nat_abs), λ _, or.inl rfl⟩
    else if 0 ≤ m
      then if 0 ≤ b.middle
        then let n := min m.to_nat b.middle.to_nat in
          ⟨(a.left + n, a.right + b.right), false.elim ∘ h⟩
        else let n := min m.to_nat b.middle.nat_abs in
          ⟨(a.left, b.right + n + m.to_nat), false.elim ∘ h⟩
      else if 0 ≤ a.middle
          then let n := min m.nat_abs a.middle.to_nat in
            ⟨(a.left + n + m.nat_abs, b.right), false.elim ∘ h⟩
          else let n := min m.nat_abs a.middle.nat_abs in
            ⟨(a.left + b.left, b.right + n), false.elim ∘ h⟩ in
⟨x.1.1, a.middle + b.middle, x.1.2, x.2⟩

instance : has_mul BS := ⟨mul⟩

@[simp] lemma int.coe_nat_le_zero (a : ℕ) : (a : ℤ) ≤ 0 ↔ a = 0 := sorry

private lemma mul_one (a  : BS) : mul a one = a :=
begin
  cases a,
  simp [mul, one],
  split_ifs; finish [nat.not_lt_zero]
end

private lemma mul_inv (a : BS) : mul a (inv a) = one :=
begin
  cases a,
  simp [mul, one, inv]
end

private lemma mul_left (a b : BS) : (mul a b).left =
  let m : ℤ := a.right - b.left in
  if h : a.middle + b.middle = 0
  then let k : ℤ := a.left + b.left - a.right - b.right in
    if 0 ≤ k
      then k.to_nat
      else 0
  else if 0 ≤ m
    then if 0 ≤ b.middle
      then a.left + min m.to_nat b.middle.to_nat
      else a.left
    else if 0 ≤ a.middle
        then a.left + min m.nat_abs a.middle.to_nat + m.nat_abs
        else a.left + b.left :=
by simp [mul]; split_ifs; simp

@[simp] private lemma mul_middle (a b : BS) : (mul a b).middle = a.middle + b.middle := rfl

private lemma mul_assoc (a b c : BS) : mul (mul a b) c = mul a (mul b c) :=
begin
  cases a, cases b, cases c,
  ext,
  { simp only [mul_left, mul_middle, add_assoc],
    dsimp,
    by_cases h : a_middle + b_middle + c_middle = 0,
    { rw [dif_pos h, dif_pos ((add_assoc _ _ _).symm.trans h)],
      split_ifs, }

  }







end



#exit
import analysis.special_functions.trigonometric

open complex real

example (θ φ : ℝ) (h1 : θ ≤ pi) (h2 : -pi < θ)
  (h3 : 0 < cos φ) : arg (exp (I * θ) * cos φ) = θ :=
by rw [mul_comm, ← of_real_cos, arg_real_mul _ h3, mul_comm,
  exp_mul_I, arg_cos_add_sin_mul_I h2 h1]



#print prod.lex
#print is_lawful_singleton



example (A B : Prop) (h : A → ¬ ¬ B) (hnnA : ¬ ¬ A) : ¬ ¬ B :=
λ hB, hnnA (λ hA, h hA hB)

lemma X : ¬ ¬ (∀ p, p ∨ ¬ p) → ∀ p, p ∨ ¬ p :=
begin
  isafe, -- goals accomplished
end
#print axioms not_forall
#print X

example : ¬¬(∀ p, p ∨ ¬ p) := by ifinish

example (A B C : Prop) :
  A ∨ B ∨ C →
  (A → ¬ B ∧ ¬ C) →
  (B → ¬ A ∧ ¬ C) →
  (C → ¬ A ∧ ¬ B) →
  (A ↔ A) →
  (B ↔ (A ∨ B)) →
  (C ↔ (B ∨ C)) →
  C :=
  λ h hA1 hB1 hC1 hA2 hB2 hC2,
have A → B, by tauto!, by tauto!

example (A B C : Prop) :
  A ∨ B ∨ C →
  (A → ¬ B ∧ ¬ C) →
  (B → ¬ A ∧ ¬ C) →
  (C → ¬ A ∧ ¬ B) →
  (A ↔ A) →
  (B ↔ (A ∨ B)) →
  (C ↔ (B ∨ C)) →
  C :=
λ h hA1 hB1 hC1 hA2 hB2 hC2,
match h with
| (or.inl hA)          := ((hA1 hA).1 (hB2.2 (or.inl hA))).elim
| (or.inr (or.inl hB)) := ((hB1 hB).2 (hC2.2 (or.inl hB))).elim
| (or.inr (or.inr hC)) := hC
end

#exit
import data.list.basic
import data.list
import tactic
import order.lexicographic

variables {α : Type*} (r : α → α → Prop) (wf : well_founded r)

lemma list.lex.cons_iff' {a₁ a₂ : α} {l₁ l₂ : list α} :
  list.lex r (a₁ :: l₁) (a₂ :: l₂) ↔ r a₁ a₂ ∨ a₁ = a₂ ∧ list.lex r l₁ l₂ :=
begin
  split,
  { assume h,
    cases h; simp * },
  { assume h,
    rcases h with hr | ⟨rfl, h⟩,
    { exact list.lex.rel hr },
    { exact list.lex.cons h } }
end

lemma lex_wf_aux : ∀ (n : ℕ),
  well_founded
    (inv_image (list.lex r)
      (subtype.val : {l : list α // l.length = n} → list α))
| 0     := subrelation.wf
  (begin
    rintros l₁ ⟨l₂, hl₂⟩,
    simp [inv_image, empty_relation, list.length_eq_zero.1 hl₂]
  end)
  empty_wf
| (n+1) :=
let f : {l : list α // l.length = n + 1} → α × {l : list α // l.length = n} :=
  λ l, (l.val.nth_le 0 (by rw [l.2]; exact nat.succ_pos _),
      subtype.mk l.1.tail $ by simp [list.length_tail, l.prop]) in
subrelation.wf
  (begin
    rintros ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩,
    cases l₁,
    { exact (nat.succ_ne_zero _ hl₁.symm).elim },
    cases l₂,
    { exact (nat.succ_ne_zero _ hl₂.symm).elim },
    simp [inv_image, list.lex.cons_iff', prod.lex_def]
  end)
  (inv_image.wf f (prod.lex_wf wf (lex_wf_aux n)))

lemma psigma.lex_def {α : Sort*} {β : α → Sort*}
  {r : α → α → Prop} {s : Π a, β a → β a → Prop} {a b : psigma β} :
  psigma.lex r s a b ↔ r a.fst b.fst ∨
  ∃ h : a.fst = b.fst, s b.fst (cast (congr_arg β h) a.snd) b.snd :=
begin
  split,
  { intro h,
    induction h; simp * },
  { intro h,
    cases a with a₁ a₂,
    cases b with b₁ b₂,
    dsimp at h,
    rcases h with hr | ⟨rfl, h⟩,
    { exact psigma.lex.left _ _ hr },
    { exact psigma.lex.right _ h } }
end
#print list.lex
lemma list.lex_wf : well_founded (list.lex r) :=
let f : list α → Σ' n : ℕ, {l : list α // l.length = n} :=
  λ l, ⟨l.length, l, rfl⟩ in
subrelation.wf (show subrelation _
    (inv_image (psigma.lex (<) (λ n, inv_image (list.lex r)
      (subtype.val : {l' : list α // l'.length = n} → list α))) f),
  begin
    intros l₁ l₂ h,
    dsimp only [inv_image, f],
    induction h with a l a l₁ l₂ h ih,
    { exact psigma.lex.left _ _ (nat.succ_pos _) },
    { rw [psigma.lex_def] at ih,
      rcases ih with hr | ⟨hl, hlex⟩,
      { exact psigma.lex.left _ _ (nat.succ_lt_succ hr) },
      { dsimp at hl,
        simp only [psigma.lex_def, lt_irrefl, hl, list.length_cons, false_or,
          exists_prop_of_true, set_coe_cast, subtype.coe_mk],
        exact list.lex.cons (by simpa [hl] using hlex) } },
    {  }

  end)
  (inv_image.wf f (psigma.lex_wf
    (show well_founded has_lt.lt, from nat.lt_wf)
    (lex_wf_aux r wf)))

def lex_wf_fun : list α → α ⊕ unit
| []     := sum.inr ()
| (a::l) := sum.inl a

#print list.lex

example {l₁ l₂ : list α} (h : list.lex r l₁ l₂) :
  prod.lex (<) (sum.lex r (λ _ _, false))
  (l₁.length, lex_wf_fun l₁)
  (l₂.length, lex_wf_fun l₂) :=
begin
  induction h,
  { simp [lex_wf_fun, prod.lex_def] },
  { simp [lex_wf_fun, prod.lex_def] at *, admit },
  { simp [lex_wf_fun, prod.lex_def, *] at * }
end

lemma acc_lex_nil : acc (list.lex r) [] :=
acc.intro _ (λ l hl, (list.lex.not_nil_right _ _ hl).elim)

lemma list.lex.cons_iff' {a₁ a₂ : α} {l₁ l₂ : list α} :
  list.lex r (a₁ :: l₁) (a₂ :: l₂) ↔ r a₁ a₂ ∨ a₁ = a₂ ∧ list.lex r l₁ l₂ :=
begin
  split,
  { assume h,
    cases h; simp * },
  { assume h,
    rcases h with hr | ⟨rfl, h⟩,
    { exact list.lex.rel hr },
    { exact list.lex.cons h } }
end

#print psigma.lex
#print pi.lex

include wf

local attribute [elab_as_eliminator] well_founded.fix

example (l : list α) : acc (list.lex r) l :=
begin
  induction l with a₁ l₁ ih,
  { exact acc_lex_nil _ },
  { refine acc.intro _ (λ l₂ hl₂, _),
    induction l₂ with a₂ l₂ ih₂,
    { exact acc_lex_nil _ },
    { rw [list.lex.cons_iff'] at hl₂,
      rcases hl₂ with hr | ⟨rfl, h⟩,
      { refine well_founded.fix wf _ a₂,
        assume x ih,
        refine acc.intro _ (λ l₃ hl₃, _),
        induction hl₃,
        { exact acc_lex_nil _ },
        {  } }

        }
     }


end

example (P : ℤ → Prop) (h8 : ∀ n, P n → P (n + 8))
  (h3 : ∀ n, P n → P (n - 3)) : ∀ n, P n → P (n + 1) :=
λ n hn, begin
  have := h8 _ (h8 _ (h3 _ (h3 _ (h3 _ (h3 _ (h3 n hn)))))),
  ring at this,
  exact this
end
#exit


#print list.lex

meta def ack_list : list ℕ → list ℕ
| [] := []
| [n] := [n]
| (n::0::l) := ack_list ((n+1)::l)
| (0::(m+1)::l) := ack_list (1::m::l)
| ((n+1)::(m+1)::l) := ack_list (n::(m+1)::m::l)


#eval ack_list [2, 3]

#exit
import algebra.ring
inductive nat2 : Type
| zero : nat2
| succ : nat2 → nat2

namespace nat2

variables {α : Type} (z : α) (s : α → α)

def lift (n : nat2) : α :=
nat2.rec_on n z (λ _, s)

@[simp] lemma lift_zero  :
  lift z s zero = z := rfl

@[simp] lemma lift_succ (n : nat2) :
  lift z s (succ n) = s (lift z s n):= rfl

attribute [irreducible] lift

lemma hom_ext {f g : nat2 → α}
  (hfz : f zero = z) (hfs : ∀ n, f (succ n) = s (f n))
  (hgz : g zero = z) (hgs : ∀ n, g (succ n) = s (g n))
  (n : nat2) :
  f n = g n :=
begin
  induction n with n ih,
  { rw [hfz, hgz] },
  { rw [hfs, hgs, ih] }
end

@[simp] lemma lift_zero_succ (n : nat2) : lift zero succ n = n :=
hom_ext zero succ (by simp) (by simp) rfl (by simp) n

def add (n : nat2) : nat2 → nat2 := lift n succ
infix ` + ` := add

-- Prove adding on the left is a hom

@[simp] lemma add_zero (n : nat2) : n + zero = n :=
lift_zero _ _

@[simp] lemma add_succ (m n : nat2) : m + succ n = succ (m + n) :=
lift_succ _ _ _

-- Prove adding on the right is a hom

@[simp] lemma zero_add (n : nat2) : zero + n = n :=
hom_ext zero succ
  (by simp [add])
  (by simp [add])
  (by simp [add])
  (λ n, by simp [add])
  n

@[simp] lemma succ_add (m n : nat2) : succ m + n = succ (m + n) :=
hom_ext (succ m) succ
  (by simp [add])
  (by simp [add])
  (by simp [add])
  (by simp [add])
  n

lemma add_comm (m n : nat2) : m + n = n + m :=
hom_ext m succ (add_zero _) (add_succ _) (zero_add _) (λ n, succ_add n m) _

lemma add_assoc (a b c : nat2): (a + b) + c = a + (b + c) :=
hom_ext (a + b) succ
  (by simp)
  (by simp)
  (by simp)
  (by simp)
  c

lemma add_left_comm (a b c : nat2): a + (b + c) = b + (a + c) :=
by rw [← add_assoc, add_comm a b, add_assoc]


def mul (n : nat2) : nat2 → nat2 := lift zero (+ n)

infix ` * ` := mul

-- Prove multiplication on the left is a hom

@[simp] lemma mul_zero (n : nat2) : n * zero = zero := by simp [mul]

@[simp] lemma mul_succ (m n : nat2) : m * succ n = (m * n) + m := by simp [mul]

-- Prove multiplication on the right is a hom

@[simp] lemma zero_mul (n : nat2) : zero * n = zero :=
hom_ext zero (+ zero)
  (by simp [mul])
  (by simp [mul])
  (by simp [mul])
  (by simp [mul])
  n

@[simp] lemma succ_mul (m n : nat2) : succ m * n = n + (m * n):=
hom_ext zero (+ m.succ)
  (by simp)
  (by simp [mul])
  (by simp [mul])
  (by simp [mul, add_comm, add_assoc])
  n

lemma mul_comm (m n : nat2) : m * n = n * m :=
hom_ext zero (+ m)
  (by simp)
  (by simp)
  (by simp)
  (by simp [add_comm])
  n

lemma mul_add (a b c : nat2) : a * (b + c) = a * b + a * c :=
@hom_ext _ zero (+ (b + c))
  (λ a, a * (b + c)) (λ a, a * b + a * c)
  (by simp)
  (by simp [add_comm])
  (by simp)
  (by simp [add_comm, add_assoc, add_left_comm])
  a

lemma add_mul (a b c : nat2) : (a + b) * c = a * c + b * c :=
by rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

lemma mul_assoc (a b c : nat2): (a * b) * c = a * (b * c) :=
hom_ext zero (+ (a * b))
  (by simp)
  (by simp)
  (by simp)
  (by simp [mul_add])
  c

lemma mul_one (a : nat2) : a * succ zero = a :=
@hom_ext _ zero succ
  (λ a, a * succ zero) id
  (by simp)
  (by simp)
  (by simp)
  (by simp)
  a

lemma one_mul (a : nat2) : succ zero * a = a :=
@hom_ext _ zero succ
  (λ a, succ zero * a) id
  (by simp)
  (by simp)
  (by simp)
  (by simp)
  a

instance : comm_semiring nat2 :=
{ zero := zero,
  one := succ zero,
  add := add,
  add_assoc := add_assoc,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  mul := mul,
  mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  zero_mul := zero_mul,
  mul_zero := mul_zero,
  mul_comm := mul_comm,
  left_distrib := mul_add,
  right_distrib := add_mul }

lemma succ_inj (a b : nat2) : succ a = succ b → a = b :=
calc a = pred (succ a) : by simp [pred]


end nat2

#exit
import data.fintype.basic data.fintype.card

import tactic

open interactive tactic expr

meta def power : tactic unit := `[sorry]

meta def sorrying_aux (e : expr) : tactic (list unit) :=
do tactic.all_goals
    (do gs ← tactic.get_goal, if gs = e then power else `[skip])

#print tactic.interactive.rewrite

meta def tactic.interactive.sorrying (q : parse types.texpr) : tactic (list unit) :=
do gs ← tactic.get_goals, h ← tactic.i_to_expr q, sorrying_aux h

example (x : ℕ) : x ≠ 0 ∧ false ∧ x ≠ 0 ∧ x ≠ 0 :=
begin
  sorrying x,
  repeat{ split },
  --sorrying (x ≠ 0), -- unknown identifier 'x'
end

def is_pos : ℕ → bool
| 0 := ff
| _ := tt
#print is_pos._main


#exit
import data.real.basic

set_option old_structure_cmd true
open_locale classical
noncomputable theory

class transmathematic (R : Type*) extends has_add R, has_div R, has_inv R, has_zero R,
  has_one R, has_neg R, has_sub R, has_mul R, has_le R, has_lt R :=
( nullity : R)
( infinity : R )
( sgn : R → R )
( sgn1 : ∀ a, a < 0 → sgn a = -1 )
( sgn2 : ∀ a, a = 0 → sgn a = 0 )
( sgn3 : ∀ a, a > 0 → sgn a = 1 )
( sgn4 : ∀ a, a = nullity → sgn a = nullity )
( A1 : ∀ a b c : R, a + (b + c) = (a + b) + c )
( A2 : ∀ a b : R, a + b = b + a )
( A3 : ∀ a : R, 0 + a = a )
( A4 : ∀ a : R, nullity + a = nullity )
( A5 : ∀ a : R, a ≠ infinity → a ≠ -infinity → a ≠ nullity → a + infinity = infinity )
( A6 : ∀ a b : R, a - b = a + (-b))
( A7 : ∀ a : R, - -a = a )
( A8 : ∀ a : R, a ≠ nullity → a ≠ infinity → a ≠ -infinity → a - a = 0)
( A9 : -nullity = nullity )
( A10 : ∀ a : R, a ≠ nullity → a ≠ infinity → a -infinity = -infinity )
( A11 : infinity - infinity = nullity )
( A12 : ∀ a b c : R, a * (b * c) = (a * b) * c )
( A13 : ∀ a b : R, a * b = b * a )
( A14 : ∀ a : R, 1 * a = a )
( A15 : ∀ a : R, nullity * a = nullity )
( A16 : infinity * 0 = nullity )
( A17 : ∀ a b : R, a / b = a * b⁻¹ )
( A18 : ∀ a : R, a ≠ nullity → a ≠ infinity → a ≠ -infinity → a ≠ 0 → a / a = 1)
( A19 : ∀ a : R, a ≠ -infinity → a⁻¹⁻¹ = a )
( A20 : 0⁻¹ = infinity )
( A21 : (-infinity)⁻¹ = 0 )
( A22 : nullity⁻¹ = nullity )
( A23 : ∀ a : R, infinity * a = infinity ↔ a > 0 )
( A24 : ∀ a : R, infinity * a = -infinity ↔ 0 > a )
( A25 : infinity > 0 )
( A26 : ∀ a b : R, a - b > 0 ↔ a > b )
( A27 : ∀ a b : R, a > b ↔ b < a )
( A28 : ∀ a b : R, a ≥ b ↔ (a > b) ∨ (a = b) )
( A29 : ∀ a b : R, a ≤ b ↔ b ≥ a )
( A30 : ∀ a : R, list.countp id [a < 0, a = 0, a > 0, a = nullity] = 1 )
( A31 : ∀ a b c : R, a ≠ infinity → a ≠ -infinity → sgn b ≠ sgn c → b + c ≠ 0 →
  b + c ≠ nullity → a * (b + c) = a * b + a * c )
( A32 : ∀ Y : set R, nullity ∉ Y → ∃ u, (∀ y ∈ Y, y ≤ u) ∧
  ∀ v : R, v ≠ nullity → (∀ y ∈ Y, y ≤ v) → u ≤ v )

inductive transreal : Type
| of_real : ℝ → transreal
| nullity : transreal
| infinity : transreal
| neg_infinity : transreal

namespace transreal

instance : has_zero transreal := ⟨of_real 0⟩
@[simp] lemma zero_def : (0 : transreal) = of_real 0 := rfl

instance : has_one transreal := ⟨of_real 1⟩
@[simp] lemma one_def : (1 : transreal) = of_real 1 := rfl

@[simp] def neg : transreal → transreal
| (of_real a) := of_real (-a)
| nullity := nullity
| neg_infinity := infinity
| infinity := neg_infinity

instance : has_neg transreal := ⟨neg⟩
@[simp] lemma neg_def (a : transreal) : -a = neg a := rfl

@[simp] def add : transreal → transreal → transreal
| (of_real a) (of_real b) := of_real (a + b)
| nullity a := nullity
| a nullity := nullity
| infinity neg_infinity := nullity
| neg_infinity infinity := nullity
| a infinity := infinity
| a neg_infinity := neg_infinity
| infinity a := infinity
| neg_infinity a := neg_infinity

instance : has_add transreal := ⟨add⟩
@[simp] lemma add_def (a b : transreal) : a + b = add a b := rfl

instance : has_sub transreal := ⟨λ a b, a + -b⟩
@[simp] lemma sub_def (a b : transreal) : a - b = a + -b := rfl

@[simp] def inv : transreal → transreal
| (of_real a) := if a = 0 then infinity else (of_real (a⁻¹))
| nullity := nullity
| neg_infinity := 0
| infinity := 0

instance : has_inv transreal := ⟨inv⟩
@[simp] lemma inv_def (a : transreal) : a⁻¹ = inv a := rfl

@[simp] def mul : transreal → transreal → transreal
| (of_real a) (of_real b) := of_real (a * b)
| nullity a := nullity
| a nullity := nullity
| infinity (of_real a) :=
  if a = 0 then nullity
    else if a < 0
      then -infinity
      else infinity
| (of_real a) infinity :=
  if a = 0 then nullity
    else if a < 0
      then -infinity
      else infinity
| neg_infinity (of_real a) :=
  if a = 0 then nullity
    else if a < 0
      then infinity
      else -infinity
| (of_real a) neg_infinity :=
  if a = 0 then nullity
    else if a < 0
      then infinity
      else -infinity
| infinity infinity := infinity
| infinity neg_infinity := neg_infinity
| neg_infinity infinity := neg_infinity
| neg_infinity neg_infinity := infinity

instance : has_mul transreal := ⟨mul⟩
@[simp] lemma mul_def (a b : transreal) : a * b = mul a b := rfl

instance : has_div transreal := ⟨λ a b, a * b⁻¹⟩
@[simp] lemma div_def (a b : transreal) : a / b = a * b⁻¹ := rfl

@[simp] def lt : transreal → transreal → Prop
| (of_real a) (of_real b) := a < b
| nullity a := false
| a nullity := false
| (of_real a) infinity := true
| neg_infinity infinity := true
| infinity infinity := false
| a neg_infinity := false
| infinity (of_real a) := false
| neg_infinity (of_real a) := true

instance : has_lt transreal := ⟨lt⟩
@[simp] lemma lt_def (a b : transreal) : a < b = lt a b := rfl

instance : has_le transreal := ⟨λ a b, a < b ∨ a = b⟩
@[simp] lemma le_def (a b : transreal) : a ≤ b = (a < b ∨ a = b) := rfl

@[simp] def sgn : transreal → transreal
| (of_real a) := if 0 < a then 1 else if a < 0 then -1 else 0
| infinity := 1
| neg_infinity := -1
| nullity := nullity

local attribute [simp] gt ge

instance : transmathematic transreal :=
{ add := (+),
  div := (/),
  inv := has_inv.inv,
  zero := 0,
  one := 1,
  sub := has_sub.sub,
  mul := (*),
  neg := has_neg.neg,
  le := (≤),
  lt := (<),
  nullity := nullity,
  infinity := infinity,
  sgn := sgn,
  sgn1 := λ a ha,
    by { cases a; simp * at *,
          simp [not_lt_of_gt ha] },
  sgn2 := λ a, by cases a; simp [lt_irrefl] {contextual := tt},
  sgn3 := λ a ha, by { cases a; simp * at * },
  sgn4 := λ a ha, by { cases a; simp * at * },
  A1 := λ a b c, by cases a; cases b; cases c; simp [add_assoc],
  A2 := λ a b, by cases a; cases b; simp [add_comm],
  A3 := λ a, by cases a; simp,
  A4 := λ a, by cases a; simp,
  A5 := λ a, by cases a; simp,
  A6 := by intros; try {cases a}; try {cases b}; try {cases c}; simp,
  A7 := by intros; try {cases a}; try {cases b}; try {cases c}; simp,
  A8 := by intros; try {cases a}; try {cases b}; try {cases c}; simp * at *,
  A9 := rfl,
  A10 := by intros; try {cases a}; try {cases b}; try {cases c}; simp * at *,
  A11 := by intros; try {cases a}; try {cases b}; try {cases c}; simp,
  A12 := begin
    assume a b c,
    cases a; simp; cases b; simp; try {split_ifs}; try{simp}; cases c;
    simp; try {split_ifs}; try {refl};
    try {simp [mul_assoc, mul_pos_iff, mul_neg_iff, eq_self_iff_true,
      or_true, *] at *}; try {split_ifs}; try {simp * at *};
    simp only [le_antisymm_iff, lt_iff_le_and_ne] at *;
    tauto,
  end,
  A13 := begin
    assume a b,
    cases a; simp; cases b; simp; try {split_ifs};
    try {refl};
    try {simp [mul_comm, mul_pos_iff, mul_neg_iff, eq_self_iff_true,
      or_true, *] at *}; try {split_ifs}; try {simp * at *};
    simp only [le_antisymm_iff, lt_iff_le_and_ne] at *;
    tauto,
  end,
  A14 := by intros; try {cases a}; try {cases b}; try {cases c}; norm_num; simp * at *,
  A15 := by intros; try {cases a}; try {cases b}; try {cases c}; simp,
  A16 := by intros; try {cases a}; try {cases b}; try {cases c}; simp,
  A17 := by intros; try {cases a}; try {cases b}; try {cases c}; simp,
  A18 := by intro a; cases a; simp {contextual := tt},
  A19 := by intro a; cases a; simp; try {split_ifs}; simp * {contextual := tt},
  A20 := by simp,
  A21 := rfl,
  A22 := rfl,
  A23 := begin
    assume a,
    cases a;
    simp; try {split_ifs};
    simp only [le_antisymm_iff, lt_iff_le_and_ne, *, ne.def, le_refl,
      false_and, or_true, true_or, and_false, or_false, false_or, true_and,
      and_true, not_true, eq_self_iff_true, true_iff, not_false_iff] at *,
    linarith,
  end,
  A24 := begin
    assume a,
    cases a;
    simp; try {split_ifs};
    simp only [le_antisymm_iff, lt_iff_le_and_ne, *, ne.def, le_refl,
      false_and, or_true, true_or, and_false, or_false, false_or, true_and,
      and_true, not_true, eq_self_iff_true, true_iff, not_false_iff] at *,
  end,
  A25 := by simp,
  A26 := λ a b, begin
    cases a; cases b; simp,
    rw [← sub_eq_add_neg, sub_pos],
  end,
  A27 := by simp,
  A28 := λ a b, by cases a; cases b; simp; simp only [le_iff_lt_or_eq, eq_comm],
  A29 := by simp,
  A30 := λ a, begin
    cases a; simp [list.countp],
    split_ifs; try {linarith},
    have := lt_trichotomy a 0,
    simp * at *,
  end,
  A31 := λ a b c, by cases a; cases b; cases c; simp; split_ifs; simp [mul_add],
  A32 := assume Y hY,
    begin
      by_cases infinity ∈ Y,
      { use infinity,
        split,
        { assume y, cases y; simp * },
        { assume v h h1,
          have := h1 infinity,
          cases v; simp * at * } },
      { by_cases hne : (of_real ⁻¹' Y).nonempty,
        { by_cases hbdd : bdd_above (of_real ⁻¹' Y),
          { use Sup (of_real ⁻¹' Y),
            split,
            { assume y hy,
              cases y; simp * at *,
              rw [← le_iff_lt_or_eq],
              exact le_cSup hbdd hy },
            { assume v hv,
              cases v; simp * at *,
              { simp only [← le_iff_lt_or_eq],
                assume h,
                refine (cSup_le_iff hbdd hne).2 (λ b hb, _),
                have := (h (of_real b) hb),
                simp [le_iff_lt_or_eq, *] at * },
              { assume h,
                cases hne with x hx,
                have := h (of_real x) hx,
                simp * at * } } },
          { use infinity,
            cases hne with x hx,
            split,
            { assume y, cases y; simp *, },
            { assume v _ h,
              have := h (of_real x) hx,
              cases v; simp * at *,
              apply hbdd,
              use v,
              assume x hx,
              simpa [le_iff_lt_or_eq] using h (of_real x) hx } } },
        { use neg_infinity,
          have : ∀ x, of_real x ∉ Y,
          { assume x hx, exact hne ⟨x, hx⟩ },
          split,
          { assume y, cases y; simp * at * },
          { assume v hv h,
            cases v; simp * at * } } }
    end }




run_cmd
do env ← tactic.get_env,
  d ← env.get `transreal.transmathematic._proof_36,
  let e := d.value,
  tactic.trace (e.to_string)


def expr.length

end transreal

#exit
import tactic

/-!

# The partition challenge!

Prove that equivalence relations on α are the same as partitions of α.

Three sections:

1) partitions
2) equivalence classes
3) the challenge

## Overview

Say `α` is a type, and `R` is a binary relation on `α`.
The following things are already in Lean:

reflexive R := ∀ (x : α), R x x
symmetric R := ∀ ⦃x y : α⦄, R x y → R y x
transitive R := ∀ ⦃x y z : α⦄, R x y → R y z → R x z

equivalence R := reflexive R ∧ symmetric R ∧ transitive R

In the file below, we will define partitions of `α` and "build some
interface" (i.e. prove some propositions). We will define
equivalence classes and do the same thing.
Finally, we will prove that there's a bijection between
equivalence relations on `α` and partitions of `α`.

-/

/-

# 1) Partitions

We define a partition, and prove some easy lemmas.

-/

/-

## Definition of a partition

Let `α` be a type. A *partition* on `α` is defined to be
the following data:

1) A set C of subsets of α, called "blocks".
2) A hypothesis (i.e. a proof!) that all the blocks are non-empty.
3) A hypothesis that every term of type α is in one of the blocks.
4) A hypothesis that two blocks with non-empty intersection are equal.
-/

/-- The structure of a partition on a Type α. -/
@[ext] structure partition (α : Type) :=
(C : set (set α))
(Hnonempty : ∀ X ∈ C, (X : set α).nonempty)
(Hcover : ∀ (a : α), ∃ X ∈ C, a ∈ X)
(Hdisjoint : ∀ X Y ∈ C, (X ∩ Y : set α).nonempty → X = Y)

/-

## Basic interface for partitions

-/

namespace partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variables {α : Type} {P : partition α} {X Y : set α}

/-- If X and Y are blocks, and a is in X and Y, then X = Y. -/
theorem eq_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a : α}
  (haX : a ∈ X)
  (haY : a ∈ Y) : X = Y :=
begin
  have h := P.Hdisjoint X Y hX hY,
  apply h,
  use a,
  split;
  assumption,
end


/-- If a is in two blocks X and Y, and if b is in X,
  then b is in Y (as X=Y) -/
theorem mem_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a b : α}
  (haX : a ∈ X) (haY : a ∈ Y) (hbX : b ∈ X) : b ∈ Y :=
begin
  convert hbX,
  exact (eq_of_mem hX hY haX haY).symm,
end

/-- Every term of type `α` is in one of the blocks for a partition `P`. -/
theorem mem_block (a : α) : ∃ X : set α, X ∈ P.C ∧ a ∈ X :=
begin
  rcases P.Hcover a with ⟨X, hXC, haX⟩,
  use X,
  split; assumption,
end

end partition

/-

# 2) Equivalence classes.

We define equivalence classes and prove a few basic results about them.

-/

section equivalence_classes

/-!

## Definition of equivalence classes

-/

-- Notation and variables for the equivalence class section:

-- let α be a type, and let R be a binary relation on R.
variables {α : Type} (R : α → α → Prop)

/-- The equivalence class of `a` is the set of `b` related to `a`. -/
def cl (a : α) :=
{b : α | R b a}

/-!

## Basic lemmas about equivalence classes

-/

/-- Useful for rewriting -- `b` is in the equivalence class of `a` iff
`b` is related to `a`. True by definition. -/
theorem cl_def {a b : α} : b ∈ cl R a ↔ R b a := iff.rfl

-- Assume now that R is an equivalence relation.
variables {R} (hR : equivalence R)
include hR

/-- x is in cl_R(x) -/
lemma mem_cl_self (a : α) :
  a ∈ cl R a :=
begin
  rw cl_def,
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  unfold reflexive at hrefl,
  apply hrefl,
end

/-- if a is in cl(b) then cl(a) ⊆ cl(b) -/
lemma cl_sub_cl_of_mem_cl {a b : α} :
  a ∈ cl R b →
  cl R a ⊆ cl R b :=
begin
  intro hab,
  rw set.subset_def,
  intro x,
  intro hxa,
  rw cl_def at *,
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  exact htrans hxa hab,
end

lemma cl_eq_cl_of_mem_cl {a b : α} :
  a ∈ cl R b →
  cl R a = cl R b :=
begin
  intro hab,
  apply set.subset.antisymm,
  { apply cl_sub_cl_of_mem_cl hR hab },
  { apply cl_sub_cl_of_mem_cl hR,
    rw cl_def at *,
    rcases hR with ⟨hrefl, hsymm, htrans⟩,
    apply hsymm,
    exact hab }
end

end equivalence_classes -- section

/-!

# 3) The challenge!

Let `α` be a type (i.e. a collection of stucff).

There is a bijection between equivalence relations on `α` and
partitions of `α`.

We prove this by writing down constructions in each direction
and proving that the constructions are two-sided inverses of one another.
-/

open partition


example (α : Type) : {R : α → α → Prop // equivalence R} ≃ partition α :=
-- We define constructions (functions!) in both directions and prove that
-- one is a two-sided inverse of the other
{ -- Here is the first construction, from equivalence
  -- relations to partitions.
  -- Let R be an equivalence relation.
  to_fun := λ R, {
    -- Let C be the set of equivalence classes for R.
    C := { B : set α | ∃ x : α, B = cl R.1 x},
    -- I claim that C is a partition. We need to check the three
    -- hypotheses for a partition (`Hnonempty`, `Hcover` and `Hdisjoint`),
    -- so we need to supply three proofs.
    Hnonempty := begin
      cases R with R hR,
      -- If X is an equivalence class then X is nonempty.
      show ∀ (X : set α), (∃ (a : α), X = cl R a) → X.nonempty,
      rintros X ⟨a, rfl⟩,
      use a,
      exact mem_cl_self hR _
    end,
    Hcover := begin
      cases R with R hR,
      -- The equivalence classes cover α
      show ∀ (a : α), ∃ (X : set α) (H : ∃ (b : α), X = cl R b), a ∈ X,
      sorry,
    end,
    Hdisjoint := begin
      cases R with R hR,
      -- If two equivalence classes overlap, they are equal.
      show ∀ (X Y : set α), (∃ (a : α), X = cl R a) →
        (∃ (b : α), Y = cl R b) → (X ∩ Y).nonempty → X = Y,
      sorry,
    end },
  -- Conversely, say P is an partition.
  inv_fun := λ P,
    -- Let's define a binary relation `R` thus:
    --  `R a b` iff *every* block containing `a` also contains `b`.
    -- Because only one block contains a, this will work,
    -- and it turns out to be a nice way of thinking about it.
    ⟨λ a b, ∀ X ∈ P.C, a ∈ X → b ∈ X, begin
      -- I claim this is an equivalence relation.
    split,
    { -- It's reflexive
      show ∀ (a : α)
        (X : set α), X ∈ P.C → a ∈ X → a ∈ X,
      sorry,
    },
    split,
    { -- it's symmetric
      show ∀ (a b : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
         ∀ (X : set α), X ∈ P.C → b ∈ X → a ∈ X,
      sorry,
    },
    { -- it's transitive
      unfold transitive,
      show ∀ (a b c : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
        (∀ (X : set α), X ∈ P.C → b ∈ X → c ∈ X) →
         ∀ (X : set α), X ∈ P.C → a ∈ X → c ∈ X,
      sorry,
    }
  end⟩,
  -- If you start with the equivalence relation, and then make the partition
  -- and a new equivalence relation, you get back to where you started.
  left_inv := begin
    rintro ⟨R, hR⟩,
    -- Tidying up the mess...
    suffices : (λ (a b : α), ∀ (c : α), a ∈ cl R c → b ∈ cl R c) = R,
      simpa,
    -- ... you have to prove two binary relations are equal.
    ext a b,
    -- so you have to prove an if and only if.
    show (∀ (c : α), a ∈ cl R c → b ∈ cl R c) ↔ R a b,
    sorry,
  end,
  -- Similarly, if you start with the partition, and then make the
  -- equivalence relation, and then construct the corresponding partition
  -- into equivalence classes, you have the same partition you started with.
  right_inv := begin
    -- Let P be a partition
    intro P,
    -- It suffices to prove that a subset X is in the original partition
    -- if and only if it's in the one made from the equivalence relation.
    ext X,
    show (∃ (a : α), X = cl _ a) ↔ X ∈ P.C,
    dsimp only,
    sorry,
  end }

/-
-- get these files with

leanproject get ImperialCollegeLondon/M40001_lean


leave this channel and go to a workgroup channel and try
folling in the sorrys.

I will come around to help.

-/

#exit
import tactic

/-!

# Tactic cheat sheet.


-- natnumgame tactics

apply,
exact (and assumption)
split
use (use `use` to make progress with `nonempty X`)



-/

/-!

## 1) Extracting information from hypotheses

-/

/-!

### 1a) cases and rcases

Many objects in Lean are pairs of data. For example, a proof
of `P ∧ Q` is stored as a pair consisting of a proof of `P` and
a proof of `Q`. The hypothesis `∃ n : ℕ, f n = 37` is stored
internally as a pair, namely a natural `n` and a proof that `f n = 37`.
Note that "hypothesis" and "proof" mean the same thing.

If `h : X` is something which is stored as a pair in Lean,
then `cases h with a b` will destroy `h` and replace it with
the two pieces of data which made up `h`, calling them `a` and `b`.

-/

example (h : ∃ n : ℕ, n ^ 2 = 2) : false :=
begin
  -- h: ∃ (n : ℕ), n ^ 2 = 2
  cases h with n hn,
  -- n: ℕ
  -- hn: n ^ 2 = 2
  sorry
end

example (P Q : Prop) (h : P ∧ Q) : P :=
begin
  -- h: P ∧ Q
  cases h with hP hQ,
  -- hP: P
  -- hQ: Q
  exact hP,
end

-- Some things are more than two pieces of data! You can do much more
-- elaborate deconstructions with the `rcases` command.

example (R : ℕ → ℕ → Prop) (hR : equivalence R) : symmetric R :=
begin
  -- hR: equivalence R
  rcases hR with ⟨hrefl, hsymm, htrans⟩,
  -- hrefl: reflexive R
  -- hsymm: symmetric R
  -- htrans: transitive R
  exact hsymm,
end

/-!

## 1b) specialize

Say you have a long hypothesis `h : ∀ n : ℕ, f n > 37 → n = 23`.
This hypothesis is a *function*. It takes as inputs a natural number n
and a proof that `f n > 37`, and then it gives as output a proof
that `n = 23`. You can feed in some inputs and specialize the function.

Say for example you you manage to prove the hypothesis `ht : f t > 37` for some natural
number `t`. Then `specialize h t ft` would change `h` to `t = 23`.

-/

example (X Y : set ℕ) (a : ℕ) (h : ∀ n : ℕ, n ∈ X → n ∈ Y) (haX : a ∈ X) : a ∈ Y :=
begin
  -- a: ℕ
  -- haX: a ∈ X
  -- h: ∀ (n : ℕ), n ∈ X → n ∈ Y
  specialize h a haX,
  -- h: a ∈ Y
  assumption,
end

/-!

# 2) Making new hypothesis

-/

/-!

## have

The `have` tactic makes a new hypothesis. The proof of the current goal
is paused and a new goal is created. Generally one should now put braces
`{ }` because if there is more than one goal then understanding what the
code is doing can get very difficult.

-/

example (a b c n : ℕ) (hn : n > 2) : a^n + b^n = c^n → a * b = 0 :=
begin
  -- ⊢ a ^ n + b ^ n = c ^ n → a * b = 0
  -- looks a bit tricky
  -- why not prove something easier first
  have ha : (a + 1) + 1 = a + 2,
  { -- ⊢ a + 1 + 1 = a + 2
    apply add_assoc,
  },
  -- ha: a + 1 + 1 = a + 2
  -- ⊢ a ^ n + b ^ n = c ^ n → a * b = 0
  sorry
end

/-!

# 3) Using hypotheses to change the goal.

-/

/-!

## 2a) rw

The generic `sub in` tactic. If `h : X = Y` then `rw h` will change all
`X`'s in the goal to `Y`'s. Also works with `h : P ↔ Q` if `P` and `Q`
are true-false statements.

-/

example (X Y : set ℕ) (hXY : X = Y) (a : ℕ) (haX : a ∈ Y) : a ∈ X :=
begin
  -- hXY: X = Y
  -- ⊢ a ∈ X
  rw hXY,
  -- hXY: X = Y
  -- ⊢ a ∈ Y
  assumption
end

-- Variants -- `rw h1 at h2`, `rw h1 at h2 ⊢`, `rw h at *`

/-!

## 2b) convert

`convert` is in some sense the opposite way of thinking to `rw`. Instead
of continually rewriting the goal until it becomes one of your assumptions,
why not just tell Lean that the assumption is basically the right answer
modulo a few loose ends, which Lean will then leave for you as new goals.

-/

example (X Y : set ℕ) (hX : 37 ∈ X) : 37 ∈ Y :=
begin
  -- hX: 37 ∈ X
  -- ⊢ 37 ∈ Y
  convert hX,
  -- ⊢ Y = X
  sorry
end

/-

# 4) Changing the goal without using hypotheses

-/

/-! ### 4a) intro and rintro -/

-- `intro` is a basic tactic for introducing hypotheses
example (P Q : Prop) : P → Q :=
begin
  -- ⊢ P → Q
  intro hP,
  -- hP: P
  -- ⊢ Q
  sorry
end

-- `rintro` is to `intro` what `rcases` is to `cases`. It enables
-- you to assume something and simultaneously take it apart.

example (f : ℕ → ℚ) : (∃ n : ℕ, f n > 37) → (∃ n : ℕ, f n > 36) :=
begin
  -- ⊢ (∃ (n : ℕ), f n > 37) → P
  rintro ⟨n, hn⟩,
  --  n: ℕ
  -- hn: f n > 37
  -- ⊢ P
  sorry,
end

/-! ## 4b) ext -/

-- `ext` is Lean's extensionality tactic. If your goal is to prove that
-- two extensional things are equal (e.g. sets, functions, binary relations)
-- then `ext a` or `ext a b` or whatever is appropriate, will turn the
-- question into the assertion that they behave in the same way. Let's look
-- at some examples

example (A B : set ℕ) : A = B :=
begin
  -- ⊢ A = B
  ext x,
  --  x : ℕ
  -- ⊢ x ∈ A ↔ x ∈ B
  sorry
end

example (X Y : Type) (f g : X → Y) : f = g :=
begin
  -- ⊢ f = g
  ext x,
  --  x : X
  -- ⊢ f x = g x
  sorry
end

example (α : Type) (R S : α → α → Prop) : R = S :=
begin
  -- ⊢ R = S
  ext a b,
  -- a b : α
  -- ⊢ R a b ↔ S a b
  sorry
end

#exit
import data.list.defs data.vector tactic
import for_mathlib.coprod



set_option profiler true
example {G : Type*} [group G] (a b : G) :
  a * b *
  a * b *
  a * b *
  a * b *
  a * b *

  a * b *
  a * b *
  a * b *
  a * b *
  a * b *a * b *
  a * b *
  a * b *
  a * b *
  a * b *a * b *
  a * b *
  a * b *
  a * b *
  a * b *a * b *
  a * b *
  a * b *
  a * b *
  a * b *a * b *
  a * b *
  a * b *
  a * b *
  a * b *a * b *
  a * b *
  a * b *
  a * b *
  a * b *a * b *
  a * b *
  a * b *
  a * b *
  a * b *a * b *
  a * b *
  a * b *
  a * b *
  a * b *a * b *
  a * b *
  a * b *
  a * b *
  a * b *
  a * b *
  a * b *
  a * b *
  a * b *
  a * b *
  b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ *
  a⁻¹ * b⁻¹ * a⁻¹
  = 1 :=
begin

  simp [mul_assoc],
  --group,

end

#eval let a =

#print vector

def reverse₂ {α : Type*} : list α → list α
| []     := []
| (a::l) := l ++ [a]

set_option profiler true

@[inline] def N : ℕ := 5000000

#eval  (list.reverse (list.range N)).length
#eval (reverse₂ (list.range N)).length


#exit
import data.equiv.basic data.list.perm data.list

open list



example (n : ℕ) : equiv.perm (fin n) ≃ { l : list (fin n) // l.nodup ∧ l.length = n } :=
{ to_fun := λ e, ⟨(fin_range n).map e, list.nodup_map e.injective (nodup_fin_range _), by simp⟩,
  inv_fun := λ l,
    { to_fun := λ i, l.1.nth_le i.1 (l.prop.2.symm ▸ i.2),
       inv_fun := λ i, ⟨l.1.index_of i, by conv_rhs { rw [← l.prop.2] };
         exact index_of_lt_length.2 sorry⟩,
      left_inv := λ ⟨_, _⟩, by simp [nth_le_index_of l.prop.1],
      right_inv := λ _, by simp },
  left_inv := λ _, equiv.ext $ λ i, begin simp, admit end,
  right_inv := λ ⟨_, _⟩, sorry }

open equiv set

example (l₁ l₂ : list ℕ) : bool := if l₁ ~ l₂ then tt else ff

@[simp] lemma set.sum_compl_symm_apply {α : Type*} {s : set α} [decidable_pred s] {x : s} :
  (equiv.set.sum_compl s).symm x = sum.inl x :=
by cases x with x hx; exact set.sum_compl_symm_apply_of_mem hx

@[simp] lemma set.sum_compl_symm_apply_compl {α : Type*} {s : set α}
  [decidable_pred s] {x : sᶜ} : (equiv.set.sum_compl s).symm x = sum.inr x :=
by cases x with x hx; exact set.sum_compl_symm_apply_of_not_mem hx

@[simp] lemma subtype_congr_apply {α : Sort*} {β : Sort*} {p : α → Prop} {q : β → Prop} (e : α ≃ β)
  (h : ∀ (a : α), p a ↔ q (e a)) (x : {x // p x}) : e.subtype_congr h x = ⟨e x, (h _).1 x.2⟩ := rfl

protected def compl {α β : Type*} {s : set α} {t : set β} [decidable_pred s] [decidable_pred t]
  (e₀ : s ≃ t) : {e : α ≃ β // ∀ x : s, e x = e₀ x} ≃ ((sᶜ : set α) ≃ (tᶜ : set β)) :=
{ to_fun := λ e, subtype_congr e
    (λ a, not_congr $ iff.intro
      (λ ha, by rw [← subtype.coe_mk a ha, e.prop ⟨a, ha⟩]; exact (e₀ ⟨a, ha⟩).prop)
      (λ ha, calc a = (e : α ≃ β).symm (e a) : by simp only [symm_apply_apply, coe_fn_coe_base]
                ... = e₀.symm ⟨e a, ha⟩ : (e : α ≃ β).injective
                  (by { rw [e.prop (e₀.symm ⟨e a, ha⟩)],
                        simp only [apply_symm_apply, subtype.coe_mk] })
                ... ∈ s : (e₀.symm ⟨_, ha⟩).prop)),
  inv_fun := λ e₁,
    subtype.mk
      (calc α ≃ s ⊕ (sᶜ : set α) : (set.sum_compl s).symm
          ... ≃ t ⊕ (tᶜ : set β) : equiv.sum_congr e₀ e₁
          ... ≃ β : set.sum_compl t)
      (λ x, by simp only [sum.map_inl, trans_apply, sum_congr_apply,
        set.sum_compl_apply_inl, set.sum_compl_symm_apply]),
  left_inv := λ e,
    begin
      ext x,
      by_cases hx : x ∈ s,
      { simp only [set.sum_compl_symm_apply_of_mem hx, ←e.prop ⟨x, hx⟩,
          sum.map_inl, sum_congr_apply, trans_apply,
          subtype.coe_mk, set.sum_compl_apply_inl] },
      { simp only [set.sum_compl_symm_apply_of_not_mem hx, sum.map_inr,
          subtype_congr_apply, set.sum_compl_apply_inr, trans_apply,
          sum_congr_apply, subtype.coe_mk] },
    end,
  right_inv := λ e, equiv.ext $ λ x, by simp only [sum.map_inr, subtype_congr_apply,
    set.sum_compl_apply_inr, function.comp_app, sum_congr_apply, equiv.coe_trans,
    subtype.coe_eta, subtype.coe_mk, set.sum_compl_symm_apply_compl] }

#exit
import set_theory.cardinal

open cardinal
universe u

@[simp] theorem mk_set {α : Type} : mk (set α) = 2 ^ mk α :=
begin
  rw [set, ← power_def Prop α, mk_Prop],
end
#exit
import linear_algebra.exterior_algebra

variables {R : Type*} [comm_semiring R] {M : Type*} [add_comm_monoid M] [semimodule R M]

/- The following gives an error: -/

#check (ring_quot.mk_alg_hom R (exterior_algebra.rel R M) :
  tensor_algebra R M →ₐ[R] exterior_algebra R M)

/- For this reason there is the following def in
   linear_algebra/exterior_algebra.lean: -/
/-
protected def quot : tensor_algebra R M →ₐ[R] exterior_algebra R M :=
  ring_quot.mk_alg_hom R _
-/

/- Similarly, this gives an error: -/
/-#check (ring_quot.mk_alg_hom R (tensor_algebra.rel R M) :
  free_algebra R M →ₐ[R] tensor_algebra R M)-/
#print tensor_algebra

attribute [semireducible] tensor_algebra
-- but the following doesn't work!
lemma quot2 : free_algebra R M →ₐ[R] tensor_algebra R M :=
  ring_quot.mk_alg_hom R (tensor_algebra.rel R M)
#exit
import analysis.ODE.gronwall

open topological_space

lemma ExNine (f : ℝ → ℝ) (s : set ℝ) : continuous f ↔ ∀ s, is_open s →  is_open (f ⁻¹' s) :=
⟨λ h _, h _, λ h _, h _⟩

#exit
import data.nat.prime
import data.fintype

#eval (@finset.univ (equiv.perm (fin 9)) _).filter _

#exit
variables {α : Sort*} {β : Sort*}

theorem forall_eq_apply_imp_iff {f : α → β} {p : β → Prop} :
  (∀ a, ∀ b, b = f a → p b) ↔ (∀ a, p (f a)) :=
⟨λ h a, h a (f a) rfl, λ h a b hba, hba.symm ▸ h a⟩

theorem piext {α : Sort*} {β γ : α → Sort*} (h : ∀ a, β a = γ a) :
  (Π a, β a) = Π a, γ a :=
by rw [show β = γ, from funext h]

#exit
import algebra.group_power data.equiv.mul_add data.vector2
#print function.swap
def word : ℕ → G
| 0 := a
| (n+1) := b * word n * b⁻¹ * a * b * (word n)⁻¹ * b⁻¹

def tower (k : ℕ) : ℕ → ℕ
| 0     := 1
| (n+1) := k ^ tower n

lemma word_eq_conj (n : ℕ) : word a b (n + 1) = mul_aut.conj (mul_aut.conj b (word a b n)) a :=
by simp [mul_aut.conj_apply, mul_aut.inv_def, mul_aut.conj_symm_apply, mul_assoc, word]

lemma pow_two_pow_eq (k n : ℕ) (H : word a b 1 = a ^ k) : a ^ (k ^ n) = (mul_aut.conj (mul_aut.conj b a) ^ n) a :=
begin
  induction n with n ih,
  { simp },
  { rw [nat.pow_succ, pow_mul, ih,
      ← mul_equiv.to_monoid_hom_apply, ← monoid_hom.map_pow,
      ← H, pow_succ' _ n, mul_aut.mul_apply, mul_equiv.to_monoid_hom_apply,
      word_eq_conj, word] }
end

lemma word_eq_power_tower (k n : ℕ) (H : word a b 1 = a ^ k) : word a b n = a ^ tower k n :=
begin
  induction n with n ih,
  { simp [word, tower] },
  { rw [tower, pow_two_pow_eq _ _ _ _ H, word_eq_conj, ih],
    simp only [← mul_equiv.to_monoid_hom_apply, monoid_hom.map_pow] }
end


#exit
import ring_theory.noetherian
#print rel_embedding.well_founded_iff_no_descending_seq
theorem set_has_maximal_iff_noetherian {R M} [ring R] [add_comm_group M] [module R M] :
  (∀(a : set $ submodule R M), a.nonempty → ∃ (M' ∈ a), ∀ (I ∈ a), M' ≤ I → I = M') ↔
    is_noetherian R M :=
iff.trans
  ⟨_,
    λ wf a ha, ⟨well_founded.min wf a ha, well_founded.min_mem _ _ _,
      λ I hI hminI, (lt_or_eq_of_le hminI).elim
        (λ h, (well_founded.not_lt_min wf _ _ hI h).elim) eq.symm⟩⟩
is_noetherian_iff_well_founded.symm
-- begin
--   rw [is_noetherian_iff_well_founded],
--   split,
--   { refine λ h, ⟨λ a, classical.by_contradiction (λ ha, _)⟩,
--     rcases h {a | ¬ acc gt a} ⟨a, ha⟩ with ⟨b, hab, hb⟩,
--     exact hab (acc.intro b
--       (λ c hcb, classical.by_contradiction
--         (λ hc, absurd hcb (hb c hc (le_of_lt hcb) ▸ lt_irrefl c)))),
--      },
--   { exact λ wf a ha, ⟨well_founded.min wf a ha, well_founded.min_mem _ _ _,
--       λ I hI hminI, (lt_or_eq_of_le hminI).elim
--         (λ h, (well_founded.not_lt_min wf _ _ hI h).elim) eq.symm⟩ }
-- end

#exit
import data.list.defs

variables {α β γ : Type}
open list

def sublists'_aux : list α → (list α → list β) → list (list β) → list (list β)
| []     f r := f [] :: r
| (a::l) f r := sublists'_aux l f (sublists'_aux l (f ∘ cons a) r)



def sublists2 (l : list α) := sublists_aux2 [] l cons

example (l : list α) (f : list α → list β → list β) :
  f [] (sublists_aux l f) = sublists_aux2 [] l f :=
begin
  induction l with a l ih generalizing f,
  { refl },
  { rw [sublists_aux2, ← ih, sublists_aux] }
end



import ring_theory.noetherian

example : is_noetherian_ring ℤ :=
begin
  split,
  assume s,


end

#exit
import data.polynomial.eval

variables {R : Type*} [comm_ring R] {S : Type*} [comm_ring S] {f : R →+* S}

open polynomial

variables {α : Type}

def interval : α → α → set α := sorry



#print convex_hull.intrv
lemma map_comp (p q : polynomial R) : map f (p.comp q) = (map f p).comp (map f q) :=
polynomial.induction_on p
  (by simp)
  (by simp {contextual := tt})
  (by simp [pow_succ', ← mul_assoc, polynomial.comp] {contextual := tt})

@[simp] def days : fin 12 → ℤ → ℕ
  | ⟨0, _⟩ _ := 31
  | ⟨1, _⟩ y := if 4 ∣ y ∧ (¬100 ∣ y ∨ 400 ∣ y) then 29 else 28
  | ⟨2, _⟩ _ := 31
  | ⟨3, _⟩ _ := 30
  | ⟨4, _⟩ _ := 31
  | ⟨5, _⟩ _ := 30
  | ⟨6, _⟩ _ := 31
  | ⟨7, _⟩ _ := 31
  | ⟨8, _⟩ _ := 30
  | ⟨9, _⟩ _ := 31
  | ⟨10, _⟩ _ := 30
  | ⟨11, _⟩ _ := 31
  | ⟨_ + 12, h⟩ _ := by linarith


#exit
inductive bad_eq {Q : Type} : Q → Q → Prop
| finish {q : Q} : bad_eq q q
| step   {a b : Q} : bad_eq a b → bad_eq a b

lemma bad_eq_eq {Q : Type} {a b : Q} : bad_eq a b → a = b :=
begin
    intro h, induction h, refl, assumption, -- OK
end

inductive U (R : Type) : Type
| wrap : R → U

lemma bad_eq_wrap {Q : Type} {a b : Q} : bad_eq (U.wrap a) (U.wrap b) → a = b :=
begin
    intro h,
    generalize hx : U.wrap a = x,
    generalize hy : U.wrap b = y,
    rw [hx, hy] at h,
    induction h,
    { cases h,
      simp * at * },
    { simp * at * }
end

open equiv

def perm_array (a : array n α) (p : perm (fin n)) : array n α := ⟨a.read ∘ p.inv_fun⟩

@[simp] lemma perm_array_one (a : array n α) : perm_array a 1 = a := by cases a; refl

open_locale classical

theorem perm_to_list {n : ℕ} {a : array n α} {p : perm (fin n)} :
    (perm_array a p).to_list ~ a.to_list :=
list.perm_iff_count.2 begin
  assume h,
  cases a,
  dsimp [perm_array, function.comp, array.to_list, array.rev_foldl,
    array.rev_iterate, array.read, d_array.rev_iterate, d_array.read,
    d_array.rev_iterate_aux],
  refine list.count


end
variables {α : Type*} [decidable_eq α]

open equiv equiv.perm

@[elab_as_eliminator] lemma swap_induction_on' [fintype α] {P : perm α → Prop} (f : perm α)
  (h1 : P 1) (ih : ∀ f x y, x ≠ y → P f → P (f * swap x y )) : P f :=
begin
  rw [← inv_inv f],
  refine @swap_induction_on _ _ _ (P ∘ has_inv.inv) f⁻¹ h1 _,
  assume f x y hxy hy,
  simp only [function.comp_app, mul_inv_rev, swap_inv],
  exact ih _ _ _ hxy hy
end


#exit
import data.bool data.quot

example {α : Type} (l : list α) (a : α) : a :: l ≠ l :=
λ h, list.no_confusion h


inductive X (α : Type) : trunc α → Type
| mk (a : trunc α) : X a
#print X.rec
lemma


#exit
import data.dfinsupp
import tactic

universes u v w

variables {ii : Type u} {jj : Type v} [decidable_eq ii] [decidable_eq jj]
variables (β : ii → jj → Type w) [Π i j, decidable_eq (β i j)]

section has_zero
variables [Π i j, has_zero (β i j)]

def to_fun (x : Π₀ (ij : ii × jj), β ij.1 ij.2) : Π₀ i, Π₀ j, β i j :=
quotient.lift_on x
  (λ x, ⟦dfinsupp.pre.mk
    (λ i, show Π₀ j : jj, β i j,
      from ⟦dfinsupp.pre.mk
        (λ j, x.to_fun (i, j))
        (x.pre_support.map prod.snd)
        (λ j, (x.3 (i, j)).elim (λ h, or.inl (multiset.mem_map.2 ⟨(i, j), h, rfl⟩)) or.inr)⟧)
    (x.pre_support.map prod.fst)
    (λ i, or_iff_not_imp_left.2 $ λ h, dfinsupp.ext $ λ j, (x.3 (i, j)).resolve_left
      (λ hij, h (multiset.mem_map.2 ⟨(i, j), hij, rfl⟩)))⟧)
  (λ a b hab, dfinsupp.ext (λ i, dfinsupp.ext (λ j, hab _)))

def inv_fun (x : Π₀ i, Π₀ j, β i j) : Π₀ (ij : ii × jj), β ij.1 ij.2 :=
quotient.lift_on x
  (λ x, ⟦dfinsupp.pre.mk (λ i : ii × jj, quotient.lift_on (x.1 i.1)
      (λ x, x.1 i.2)
      (λ a b hab, hab _))
    (x.pre_support.bind (λ i, (quotient.lift_on (x.1 i)
      (λ x, ((x.pre_support.filter (λ j, x.1 j ≠ 0)).map (λ j, (i, j))).to_finset)
      (λ a b hab, begin
          ext p,
          cases a, cases b,
          replace hab : a_to_fun = b_to_fun := funext hab,
          subst hab,
          cases p with p₁ p₂,
          simp [and_comm _ (_ = p₂), @and.left_comm _ (_ = p₂)],
          specialize b_zero p₂,
          specialize a_zero p₂,
          tauto,
      end)).1))
    (λ i, or_iff_not_imp_right.2 begin
      generalize hxi : x.1 i.1 = a,
      revert hxi,
      refine quotient.induction_on a (λ a hxi, _),
      assume h,
      have h₁ := (a.3 i.2).resolve_right h,
      have h₂ := (x.3 i.1).resolve_right (λ ha, begin
        rw [hxi] at ha,
        exact h ((quotient.exact ha) i.snd),
      end),
      simp only [exists_prop, ne.def, multiset.mem_bind],
      use i.fst,
      rw [hxi, quotient.lift_on_beta],
      simp only [multiset.mem_erase_dup, multiset.to_finset_val,
        multiset.mem_map, multiset.mem_filter],
      exact ⟨h₂, i.2, ⟨h₁, h⟩, by cases i; refl⟩
    end)⟧)
  (λ a b hab, dfinsupp.ext $ λ i, by unfold_coes; simp [hab i.1])

example : (Π₀ (ij : ii × jj), β ij.1 ij.2) ≃ Π₀ i, Π₀ j, β i j :=
{ to_fun := to_fun β,
  inv_fun := inv_fun β,
  left_inv := λ x, quotient.induction_on x (λ x, dfinsupp.ext (λ i, by cases i; refl)),
  right_inv := λ x, quotient.induction_on x (λ x, dfinsupp.ext (λ i, dfinsupp.ext (λ j,
    begin
      generalize hxi : x.1 i = a,
      revert hxi,
      refine quotient.induction_on a (λ a hxi, _),
      rw [to_fun, inv_fun],
      unfold_coes,
      simp,
      rw [hxi, quotient.lift_on_beta, quotient.lift_on_beta],
    end)))  }

end has_zero

section add_comm_monoid
variable [Π i j, add_comm_monoid (β i j)]
example : (Π₀ (ij : ii × jj), β ij.1 ij.2) ≃+ Π₀ i, Π₀ j, β i j :=

end add_comm_monoid


#exit
example : (Π₀ (ij : ii × jj), β ij.1 ij.2) ≃ Π₀ i, Π₀ j, β i j := sorry

example {α : Type} (r : α → α → Prop) (a : α) (h : acc r a) : acc r a :=
acc.intro _ (acc.rec_on h (λ x h ih y hy, h y hy))

variables (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] (g : G)

/-- The subfield fixed by one element of the group. -/
def fixed_by : set F :=
{ x | g • x = x }

theorem fixed_eq_Inter_fixed_by : fixed_points G F = ⋂ g : G, fixed_by G F g :=
set.ext $ λ x, ⟨λ hx, set.mem_Inter.2 $ λ g, hx g,
  λ hx g, by { exact (set.mem_Inter.1 hx g : _) } ⟩

import tactic data.real.basic

example (a b c : ℝ) (h: a/b = a/c) (g : a ≠ 0) : 1/b = 1/c :=
by rwa [← mul_right_inj' g, one_div_eq_inv, one_div_eq_inv]


import data.nat.modeq

example : unit ≠ bool :=
begin
  assume h,
  have : ∀ x y : unit, x = y, { intros, cases x, cases y, refl },
  rw h at this,
  exact absurd (this tt ff) dec_trivial

end

example (p : ℕ) (hp : p % 4 = 2) : 4 ∣ p - 2 :=
⟨p / 4, _⟩

#exit
import tactic

open set

class topological_space (X : Type) :=
(is_open        : set X → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀ (U V : set X), is_open U → is_open V → is_open (U ∩ V))
(is_open_sUnion : ∀ (𝒞 : set (set X)), (∀U ∈ 𝒞, is_open U) → is_open (⋃₀ 𝒞))

namespace topological_space

variables {X : Type} [topological_space X]

lemma open_iff_locally_open (V : set X) :
  is_open V ↔ ∀ x : X, x ∈ V → ∃ U : set X, x ∈ U ∧ is_open U ∧ U ⊆ V :=
begin
  split,
  { intro hV,
    intros x hx,
     use [V, hx, hV] },
  { intro h,
    let 𝒞 : set (set X) := {U : set X | ∃ (x : X) (hx : x ∈ V), U = classical.some (h x hx)},
    have h𝒞 : ∀ U ∈ 𝒞, ∃ (x : X) (hx : x ∈ V), x ∈ U ∧ is_open U ∧ U ⊆ V,
    { intros U hU,
      rcases hU with ⟨x, hx, rfl⟩,
      use [x, hx],
      exact classical.some_spec (h x hx) },
    convert is_open_sUnion 𝒞 _,
    { ext x, split,
      { intro hx,
        rw mem_sUnion,
        use classical.some (h x hx),
        split,
          use [x, hx],
        have h := classical.some_spec (h x hx),
        exact h.1 },
      { intro hx,
        rw mem_sUnion at hx,
        rcases hx with ⟨U, hU, hxU⟩,
        rcases h𝒞 U hU with ⟨_, _, _, _, hUV⟩,
        apply hUV,
        exact hxU }},
    { intros U hU,
      rcases (h𝒞 U hU) with ⟨_, _, _, hU, _⟩,
      exact hU },
  },
end


set_option old_structure_cmd true

namespace lftcm

/-- `monoid M` is the type of monoid structures on a type `M`. -/
class monoid (M : Type) extends has_mul M, has_one M :=
(mul_assoc : ∀ (a b c : M), a * b * c = a * (b * c))
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)

lemma one_mul {M : Type} [monoid M] (a : M) : 1 * a = a := monoid.one_mul _

lemma mul_assoc {M : Type} [monoid M] (a b c : M) :
  a * b * c = a * (b * c) := monoid.mul_assoc _ _ _

/-- `group G` is the type of group structures on a type `G`. -/
class group (G : Type) extends monoid G, has_inv G :=
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

namespace group

variables {G : Type} [group G]

lemma mul_left_cancel (a b c : G) (Habac : a * b = a * c) : b = c :=
 calc b = 1 * b         : by rw lftcm.one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : begin rw lftcm.mul_assoc, end -- ??
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : begin rw mul_assoc, refl, end -- ??
    ... = 1 * c         : by rw mul_left_inv
    ... = c             : by rw one_mul

#exit
import data.polynomial
open polynomial

#print eval₂_hom
variables {R S T : Type} [comm_ring R] [comm_ring S] [comm_ring T]

noncomputable def eval₂' (f : R →+* S) (x : S) : polynomial R →+* S :=
by refine_struct { to_fun := polynomial.eval₂ f x }; simp

lemma eq_eval₂' (i : polynomial R →+* S) :
  i = eval₂' (i.comp (ring_hom.of C)) (i X) :=
begin
  ext f,
  apply polynomial.induction_on f; simp [eval₂'] {contextual := tt},
end

example {f : R →+* S} {g : S →+* T} {p : polynomial R} (x : S):
  eval₂' (g.comp f) (g x) p = g (eval₂' f x p) :=
begin
  conv_rhs { rw [← ring_hom.comp_apply, eq_eval₂' (g.comp (eval₂' f x))] },
  simp,
end

#exit
import data.nat.digits

lemma nat.div_lt_of_le : ∀ {n m k : ℕ} (h0 : n > 0) (h1 : m > 1) (hkn : k ≤ n), k / m < n
| 0     m k h0 h1 hkn := absurd h0 dec_trivial
| 1     m 0 h0 h1 hkn := by rwa nat.zero_div
| 1     m 1 h0 h1 hkn :=
  have ¬ (0 < m ∧ m ≤ 1), from λ h, absurd (@lt_of_lt_of_le ℕ
    (show preorder ℕ, from @partial_order.to_preorder ℕ (@linear_order.to_partial_order ℕ nat.linear_order))
     _ _ _ h1 h.2) dec_trivial,
  by rw [nat.div_def_aux, dif_neg this]; exact dec_trivial
| 1     m (k+2) h0 h1 hkn := absurd hkn dec_trivial
| (n+2) m k h0 h1 hkn := begin
  rw [nat.div_def_aux],
  cases decidable.em (0 < m ∧ m ≤ k) with h h,
  { rw [dif_pos h],
    refine nat.succ_lt_succ _,
    refine nat.div_lt_of_le (nat.succ_pos _) h1 _,
    cases m with m,
    { exact absurd h.1 dec_trivial },
    { cases m with m,
      { exact absurd h1 dec_trivial },
      { clear h1 h,
        induction m with m ih,
        { cases k with k,
          { exact nat.zero_le _ },
          { cases k with k,
            { exact nat.zero_le _ },
            { rw [nat.sub_succ, nat.sub_succ, nat.sub_zero, nat.pred_succ,
                nat.pred_succ],
              exact @linear_order.le_trans ℕ nat.linear_order _ _ _
                (nat.le_succ k) (nat.le_of_succ_le_succ hkn) } } },
        { cases k with k,
          { rw [nat.zero_sub], exact nat.zero_le _ },
          { rw [nat.succ_sub_succ],
            refine @linear_order.le_trans ℕ nat.linear_order _ _ _ _ ih,
            refine nat.sub_le_sub_right _ _,
            exact nat.le_succ _ } } } } },
  { rw dif_neg h,
    exact nat.succ_pos _ }
end

lemma nat.div_lt_self'' {n m : ℕ} (h0 : n > 0)  (hm : m > 1) : n / m < n :=
nat.div_lt_of_le h0 hm (le_refl _)

def f : ℕ → ℕ
| n :=
  if h : 0 < n
  then have n - 1 < n, from nat.sub_lt h zero_lt_one,
    f (n - 1)
  else 0

def digits_aux' (b : ℕ) (h : 2 ≤ b) : ℕ → list ℕ
| 0 := []
| (n+1) :=
  have (n+1)/b < n+1 := nat.div_lt_self'' (nat.succ_pos _) h,
  (n+1) % b :: digits_aux' ((n+1)/b)

def digits' : ℕ → ℕ → list ℕ
| 0 := digits_aux_0
| 1 := digits_aux_1
| (b+2) := digits_aux' (b+2) dec_trivial

theorem test (b n : ℕ) : digits' (b+2) (n+1) = (n+1)%(b+2) :: digits' (b+2) ((n+1)/(b+2)) := rfl -- works
theorem test' : digits' (0+2) (1+1) = (1+1)%(0+2) :: digits' (0+2) ((1+1)/(0+2)) := rfl

--#reduce digits (0+2) ((1+1)/(0+2))
variables (b n : ℕ)
#reduce digits' (b+2) (n+1)

#exit
import ring_theory.ideals
import ring_theory.principal_ideal_domain
import ring_theory.localization
import tactic
import order.bounded_lattice
import algebra.field_power
import order.conditionally_complete_lattice
universe u

class discrete_valuation_ring (R : Type u) [integral_domain R] [is_principal_ideal_ring R] :=
(prime_ideal' : ideal R)
(primality : prime_ideal'.is_prime)
(is_nonzero : prime_ideal' ≠ ⊥)
(unique_nonzero_prime_ideal : ∀ P : ideal R, P.is_prime → P = ⊥ ∨ P = prime_ideal')

namespace discrete_valuation_ring

def prime_ideal (R : Type u) [integral_domain R] [is_principal_ideal_ring R] [discrete_valuation_ring R] : ideal R :=
discrete_valuation_ring.prime_ideal'

instance is_prime (R : Type*) [integral_domain R] [is_principal_ideal_ring R] [discrete_valuation_ring R] : (prime_ideal R).is_prime :=
primality

variables {R : Type u} [integral_domain R] [is_principal_ideal_ring R] [discrete_valuation_ring R]
open discrete_valuation_ring

lemma prime_ideal_is_maximal : (prime_ideal R).is_maximal :=
begin
  have f : prime_ideal R ≠ ⊥,
  { apply discrete_valuation_ring.is_nonzero },
  apply is_prime.to_maximal_ideal,
    exact f,
end

lemma unique_max_ideal : ∃! I : ideal R, I.is_maximal :=
begin
  use prime_ideal R,
  split,
  { exact prime_ideal_is_maximal },
  { intros y a,
    cases discrete_valuation_ring.unique_nonzero_prime_ideal y a.is_prime,
    { exfalso,
      rw h at a,
      apply discrete_valuation_ring.primality.left,
      exact a.right (prime_ideal R) (bot_lt_iff_ne_bot.2 discrete_valuation_ring.is_nonzero) },
    { assumption } }
end

instance is_local_ring : local_ring R := local_of_unique_max_ideal unique_max_ideal

open local_ring

noncomputable theory
open_locale classical
class discrete_valuation_field (K : Type*) [field K] :=
(v : K -> with_top ℤ )
(mul : ∀ (x y : K), v(x*y) = v(x) + v(y) )
(add : ∀ (x y : K), min (v(x)) (v(y)) ≤ v(x + y)  )
(non_zero : ∀ (x : K), v(x) = ⊤ ↔ x = 0 )

namespace discrete_valuation_field

definition valuation (K : Type*) [field K] [ discrete_valuation_field K ] : K -> with_top ℤ := v

variables {K : Type*} [field K] [discrete_valuation_field K]

lemma with_top.cases (a : with_top ℤ) : a = ⊤ ∨ ∃ n : ℤ, a = n :=
begin
  cases a with n,
  { -- a = ⊤ case
    left,
    refl, -- true by definition
  },
  { -- ℤ case
    right,
    use n,
    refl, -- true by definition
  }
end

lemma sum_zero_iff_zero (a : with_top ℤ) : a + a = 0 ↔ a = 0 :=
begin
  split,
  { -- the hard way
    intro h, -- h is a proof of a+a=0
    -- split into cases
    cases (with_top.cases a) with htop hn,
    { -- a = ⊤
      rw htop at h,
      -- h is false
      cases h,
      -- no cases!
    },
    { -- a = n
      cases hn with n hn,
      rw hn at h ⊢,
      -- now h says n+n=0 and our goal is n=0
      -- but these are equalities in `with_top ℤ
      -- so we need to get them into ℤ
      -- A tactic called `norm_cast` does this
     norm_cast at h ⊢,
      -- we finally have a hypothesis n + n = 0
      -- and a goal n = 0
      -- and everything is an integer
      rw add_self_eq_zero at h,
      assumption
    }
  },
   { -- the easy way
    intro ha,
    rw ha,
    simp
  }
end
 --Thanks Kevin!

lemma val_one_eq_zero : v(1 : K) = 0 :=
begin
  have h : (1 : K) * 1 = 1,
    simp,
  apply_fun v at h,
  rw mul at h,
  -- now we know v(1)+v(1)=v(1) and we want to deduce v(1)=0 (i.e. rule out v(1)=⊤)
  rcases (with_top.cases (v(1:K))) with h1 | ⟨n, h2⟩, -- do all the cases in one go
  { rw non_zero at h1,
    cases (one_ne_zero h1)
  },
  { rw h2 at *,
    norm_cast at *,
    -- library_search found the next line
    exact add_left_eq_self.mp (congr_arg (has_add.add n) (congr_arg (has_add.add n) h)),
  },
end

lemma val_minus_one_is_zero : v((-1) : K) = 0 :=
begin
have f : (-1:K)*(-1:K) = (1 : K),
simp,
have g : v((-1 : K)*(-1 : K)) = v(1 : K),
simp,
have k : v((-1 : K)*(-1 : K)) = v(-1 : K) + v(-1 : K),
{
  apply mul,
},
rw k at g,
rw val_one_eq_zero at g,
rw <-sum_zero_iff_zero,
exact g,
end

@[simp] lemma val_zero : v(0:K) = ⊤ :=
begin
rw non_zero,
end


lemma with_top.transitivity (a b c : with_top ℤ) : a ≤ b -> b ≤ c -> a ≤ c :=
begin
rintros,
cases(with_top.cases c) with h1 h2,
  {
    rw h1,
    simp,
  },
  {
    cases h2 with n h2,
    cases(with_top.cases a) with k1 k2,
    {
      rw [k1, h2],
      rw k1 at a_1,
      rw h2 at a_2,
      cases(with_top.cases b) with l1 l2,
      {
        rw l1 at a_2,
        exact a_2,
      },
      {
        cases l2 with m l2,
        rw l2 at a_1,
        exfalso,
        apply with_top.not_top_le_coe m,
        exact a_1,
      },
    },
    {
      cases k2 with m k2,
      cases(with_top.cases b) with l1 l2,
      {
        rw [l1,h2] at a_2,
        exfalso,
        apply with_top.not_top_le_coe n,
        exact a_2,
      },
      {
        cases l2 with k l2,
        rw [k2,l2] at a_1,
        rw [l2,h2] at a_2,
        rw [k2,h2],
        rw with_top.coe_le_coe,
        rw with_top.coe_le_coe at a_1,
        rw with_top.coe_le_coe at a_2,
        transitivity k,
        exact a_1,
        exact a_2,
      },
    },
  },
end

def val_ring (K : Type*) [field K] [discrete_valuation_field K] := { x : K | 0 ≤ v x }

instance (K : Type*) [field K] [discrete_valuation_field K] : is_add_subgroup (val_ring K) :=
{
  zero_mem := begin
              unfold val_ring,
              simp,
              end,
  add_mem := begin
            unfold val_ring,
            simp only [set.mem_set_of_eq],
            rintros,
            have g : min (v(a)) (v(b)) ≤ v(a + b),
            {
              apply add,
            },
            rw min_le_iff at g,
            cases g,
            {
              exact with_top.transitivity _ _ _ a_1 g,
            },
            {
              exact with_top.transitivity _ _ _ a_2 g,
            },
            end,
  neg_mem := begin
            unfold val_ring,
            rintros,
            simp only [set.mem_set_of_eq],
            simp only [set.mem_set_of_eq] at a_1,
            have f : -a = a * (-1 : K) := by simp,
            rw [f, mul, val_minus_one_is_zero],
            simp [a_1],
            end,
}

instance (K:Type*) [field K] [discrete_valuation_field K] : is_submonoid (val_ring K) :=
{ one_mem := begin
            unfold val_ring,
            simp,
            rw val_one_eq_zero,
            norm_num,
            end,
  mul_mem := begin
            unfold val_ring,
            rintros,
            simp,
            simp at a_1,
            simp at a_2,
            rw mul,
            apply add_nonneg' a_1 a_2,
            end, }

instance valuation_ring (K:Type*) [field K] [discrete_valuation_field K] : is_subring (val_ring K) :=
{}

instance is_domain (K:Type*) [field K] [discrete_valuation_field K] : integral_domain (val_ring K) :=
subring.domain (val_ring K)

def unif (K:Type*) [field K] [discrete_valuation_field K] : set K := { π | v π = 1 }

variables (π : K) (hπ : π ∈ unif K)

lemma val_unif_eq_one (hπ : π ∈ unif K) : v(π) = 1 :=
begin
unfold unif at hπ,
simp at hπ,
exact hπ,
end

lemma unif_ne_zero (hπ : π ∈ unif K) : π ≠ 0 :=
begin
simp,
      unfold unif at hπ,
      simp at hπ,
      intro g,
      rw <-non_zero at g,
      rw hπ at g,
      cases g,
end

lemma with_top.add_happens (a b c : with_top ℤ) (ne_top : a ≠ ⊤) : b=c ↔ a+b = a+c :=
begin
cases with_top.cases a,
{
  exfalso,
  apply ne_top,
  exact h,
},
cases h with n h,
rw h,
split,
{
  rintros,
  rw a_1,
},
cases with_top.cases b,
{
  rw h_1,
  rw with_top.add_top,
  rintros,
  have b_1 : ↑n + c = ⊤,
  exact eq.symm a_1,
  rw with_top.add_eq_top at b_1,
  cases b_1,
  {
    exfalso,
    apply with_top.coe_ne_top,
    {
      exact b_1,
    },
  },
  exact eq.symm b_1,
},
{
  cases h_1 with m h_1,
  rw h_1,
  cases with_top.cases c,
  {
    rw h_2,
    rintros,
    rw with_top.add_top at a_1,
    rw with_top.add_eq_top at a_1,
    cases a_1,
    {
      exfalso,
      apply with_top.coe_ne_top,
      exact a_1,
    },
    {
      exact a_1,
    },
  },
  cases h_2 with l h_2,
  rw h_2,
  rintros,
  norm_cast,
  norm_cast at a_1,
  simp at a_1,
  assumption,
}
end

lemma with_top.add_le_happens (a b c : with_top ℤ) (ne_top : a ≠ ⊤) : b ≤ c ↔ a + b ≤ a+c :=
begin
 rcases(with_top.cases a) with rfl | ⟨a, rfl⟩;
 rcases(with_top.cases b) with rfl | ⟨b, rfl⟩;
 rcases(with_top.cases c) with rfl | ⟨n, rfl⟩;
 try {simp},
 simp at ne_top,
 assumption,
 simp at ne_top,
 exfalso,
 assumption,
 rw <-with_top.coe_add,
 apply with_top.coe_ne_top,
 repeat{rw <-with_top.coe_add,},
 rw with_top.coe_le_coe,
 simp,
end

lemma with_top.distrib (a b c : with_top ℤ) (na : a ≠ ⊤) (nb : b ≠ ⊤) (nc : c ≠ ⊤) : (a + b)*c = a*c + b*c :=
begin
  rcases(with_top.cases a) with rfl | ⟨a, rfl⟩;
  rcases(with_top.cases b) with rfl | ⟨b, rfl⟩;
  rcases(with_top.cases c) with rfl | ⟨n, rfl⟩;
  try {simp},
  repeat
  {
  simp at na,
  exfalso,
  exact na,
  },
  {
  simp at nb,
  exfalso,
  exact nb,
  },
  {
  simp at nc,
  exfalso,
  exact nc,
  },
  rw <-with_top.coe_add,
  repeat {rw <-with_top.coe_mul},
  rw <-with_top.coe_add,
  rw with_top.coe_eq_coe,
  rw right_distrib,
end

lemma one_mul (a : with_top ℤ) : 1 * a = a :=
begin
cases (with_top.cases) a with a ha,
{
  rw a,
  simp,
},
{
  cases ha with n ha,
  rw ha,
  norm_cast,
  simp,
}
end

lemma nat_ne_top (n :ℕ) : (n : with_top ℤ) ≠ ⊤ :=
begin
simp,
end

lemma val_inv (x : K) (nz : x ≠ 0) : v(x) + v(x)⁻¹ = 0 :=
begin
rw <- mul,
rw mul_inv_cancel,
{
  rw val_one_eq_zero,
},
exact nz,
end

lemma with_top.sub_add_eq_zero (n : ℕ) : ((-n : ℤ) : with_top ℤ) + (n : with_top ℤ) = 0 :=
begin
rw <-with_top.coe_nat,
rw <-with_top.coe_add,
simp only [add_left_neg, int.nat_cast_eq_coe_nat, with_top.coe_zero],
end

lemma with_top.add_sub_eq_zero (n : ℕ) : (n : with_top ℤ) + ((-n : ℤ) : with_top ℤ) = 0 :=
begin
rw <-with_top.coe_nat,
rw <-with_top.coe_add,
simp only [add_right_neg, int.nat_cast_eq_coe_nat, with_top.coe_zero],
end

lemma contra_non_zero (x : K) (n : ℕ) (nz : n ≠ 0) : v(x^n) ≠ ⊤ ↔ x ≠ 0 :=
begin
split,
{
  contrapose,
  simp,
  intro,
  rw a,
  rw zero_pow',
  {
    exact val_zero,
  },
  {
    exact nz,
  },
},
{
  contrapose,
  simp,
  intro,
  rw non_zero at a,
  contrapose a,
  apply pow_ne_zero,
  exact a,
},
end


lemma contra_non_zero_one (x : K) : v(x) ≠ ⊤ ↔ x ≠ 0 :=
begin
split,
{
  intro,
  rw <-pow_one x at a,
  rw contra_non_zero x 1 at a,
  exact a,
  simp,
},
{
  contrapose,
  simp,
  rw non_zero,
  simp,
},
end

lemma val_nat_power (a : K) (nz : a ≠ 0) : ∀ n : ℕ, v(a^n) = (n : with_top ℤ)*v(a) :=
begin
rintros,
induction n with d hd,
{
  rw pow_zero,
  rw val_one_eq_zero,
  simp,
},
{
  rw nat.succ_eq_add_one,
  rw pow_succ',
  rw mul,
  rw hd,
  norm_num,
  rw with_top.distrib,
  rw one_mul,
  apply nat_ne_top,
  apply with_top.one_ne_top,
  intro,
  rw non_zero at a_1,
  apply nz,
  exact a_1,
}
end

lemma val_int_power (a : K) (nz : a ≠ 0) : ∀ n : ℤ, v(a^n) = (n : with_top ℤ)*v(a) :=
begin
rintros,
cases n,
{
  rw fpow_of_nat,
  rw val_nat_power,
  {
    simp only [int.of_nat_eq_coe],
    rw <-with_top.coe_nat,
    simp only [int.nat_cast_eq_coe_nat],
  },
  exact nz,
},
{
  simp only [fpow_neg_succ_of_nat],
  rw nat.succ_eq_add_one,
  rw with_top.add_happens (v (a ^ (n + 1))) (v (a ^ (n + 1))⁻¹) (↑-[1+ n] * v a),
  {
    rw val_inv,
    {
      rw val_nat_power,
      {
        simp only [nat.cast_add, nat.cast_one],
        rw <-with_top.distrib,
        {
          simp only [zero_eq_mul],
          left,
          rw int.neg_succ_of_nat_coe',
          rw sub_eq_add_neg,
          rw with_top.coe_add,
          rw add_comm (↑-↑n),
          rw <-add_assoc,
          rw add_comm,
          rw add_assoc,
          rw <-with_top.coe_one,
          rw <-with_top.coe_add,
          simp,
          rw with_top.sub_add_eq_zero,
          },
          {
            norm_cast,
            apply with_top.nat_ne_top,
          },
          {
            simp,
          },
          {
            intro,
            simp_rw [non_zero, nz] at a_1,
            exact a_1,
          },
      },
      {
        exact nz,
      },
    },
    {
      apply pow_ne_zero,
      exact nz,
    },
  },
  {
    rw contra_non_zero,
    {
      exact nz,
    },
    {
      simp,
    },
  },
},
end

lemma unit_iff_val_zero (α : K) (hα : α ∈ val_ring K) (nzα : α ≠ 0) : v (α) = 0 ↔ ∃ β ∈ val_ring K, α * β = 1 :=
begin
split,
{
  rintros,
  use α⁻¹,
  split,
  {
    {
      unfold val_ring,
      simp,
      rw <-with_top.coe_zero,
      rw with_top.coe_le_iff,
      rintros,
      rw with_top.add_happens (v(α)) _ _ at a_1,
      {
        rw val_inv at a_1,
        {
          rw a at a_1,
          simp only [with_top.zero_eq_coe, zero_add] at a_1,
          rw a_1,
        },
        exact nzα,
      },
      simp_rw [contra_non_zero_one],
      exact nzα,
    },
  },
  {
    rw mul_inv_cancel,
    exact nzα,
  },
},
{
  rintros,
  cases a with b a,
  simp at a,
  cases a,
  unfold val_ring at a_left,
  simp at a_left,
  have f : v((α)*(b)) = v(1:K),
  {
    rw a_right,
  },
  rw mul at f,
  rw val_one_eq_zero at f,
  rw add_eq_zero_iff' at f,
  {
    cases f,
    exact f_left,
  },
  {
    erw val_ring at hα,
    simp at hα,
    exact hα,
  },
  {
    exact a_left,
  },
},
end

lemma val_eq_iff_asso (x y : K) (hx : x ∈ val_ring K) (hy : y ∈ val_ring K) (nzx : x ≠ 0) (nzy : y ≠ 0) : v(x) = v(y) ↔ ∃ β ∈ val_ring K, v(β) = 0 ∧ x * β = y :=
begin
split,
intros,
use (x⁻¹*y),
{
  {
    unfold val_ring,
    simp,
    rw mul,
    rw with_top.add_happens (v(x⁻¹)) _ _ at a,
    {
      rw add_comm at a,
      rw val_inv at a,
      {
        rw <-a,
        norm_num,
        rw mul_inv_cancel_assoc_right,
        exact nzx,
      },
      exact nzx,
    },
    {
      intro f,
      rw non_zero at f,
      simp at f,
      apply nzx,
      exact f,
    },
  },
},
{
  rintros,
  cases a with z a,
  simp at a,
  cases a,
  cases a_right with a_1 a_2,
  apply_fun v at a_2,
  rw mul at a_2,
  rw a_1 at a_2,
  simp at a_2,
  exact a_2,
},
end

lemma unif_assoc (x : K) (hx : x �� val_ring K) (nz : x ≠ 0) (hπ : π ∈ unif K) : ∃ β ∈ val_ring K, (v(β) = 0 ∧ ∃! n : ℤ, x * β = π^n) :=
begin
have hπ' : π ≠ 0,
{
  apply unif_ne_zero,
  exact hπ,
},
unfold unif at hπ,
simp at hπ,
cases (with_top.cases) (v(x)),
{
 rw non_zero at h,
 exfalso,
 apply nz,
 exact h,
},
{
  cases h with n h,
  split,
  let y := x⁻¹ * π^n,
  have g : v(y) = 0,
  {
    rw [mul, val_int_power π, hπ, add_comm],
    norm_cast,
    simp,
    rw [<-h, val_inv],
    exact nz,
    exact hπ',
  },
  have f : y ∈ val_ring K,
  {
    unfold val_ring,
    simp,
    rw g,
    norm_num,
  },
  {
    use f,
    split,
    {
      exact g,
    },
    rw mul_inv_cancel_assoc_right,
    use n,
    {
      split,
      simp only [eq_self_iff_true],
      rintros,
      apply_fun v at a,
      rw [val_int_power, val_int_power, hπ] at a,
      {
        norm_cast at a,
        simp at a,
        exact eq.symm a,
      },
      exact hπ',
      exact hπ',
    },
    exact nz,
  },
},
end

lemma blah (n : ℤ) : n < n -> false :=
begin
simp only [forall_prop_of_false, not_lt],
end

lemma val_is_nat (hπ : π ∈ unif K) (x : val_ring K) (nzx : x ≠ 0) : ∃ m : ℕ, v(x:K) = ↑m :=
begin
cases with_top.cases (v(x:K)),
{
  rw h,
  simp,
  rw non_zero at h,
  apply nzx,
  exact subtype.eq h,
},
{
  cases h with n h,
  cases n,
  {
    use n,
    simp_rw h,
    simp,
    rw <-with_top.coe_nat,
    simp,
  },
  {
    have H : 0 ≤ v(x:K),
    exact x.2,
    rw h at H,
    norm_cast at H,
    exfalso,
    contrapose H,
    simp,
    tidy,
    exact int.neg_succ_lt_zero n,
  },
},
end

lemma is_pir (hπ : π ∈ unif K) : is_principal_ideal_ring (val_ring K) :=
begin
split,
rintros,
rintros,
by_cases S = ⊥,
{
  rw h,
  use 0,
  apply eq.symm,
  rw submodule.span_singleton_eq_bot,
},
let Q := {n : ℕ | ∃ x ∈ S, (n : with_top ℤ) = v(x:K) },
have g : v(π ^(Inf Q)) = ↑(Inf Q),
{
  rw val_nat_power,
  rw val_unif_eq_one,
  rw <-with_top.coe_one,
  rw <-with_top.coe_nat,
  rw <-with_top.coe_mul,
  rw mul_one,
  exact hπ,
  apply unif_ne_zero,
  exact hπ,
},
have nz : π^(Inf Q) ≠ 0,
{
  assume a,
  apply_fun v at a,
  rw g at a,
  rw val_zero at a,
  apply with_top.nat_ne_top (Inf Q),
  exact a,
},
use π^(Inf Q),
{
  unfold val_ring,
  simp,
  rw g,
  rw <-with_top.coe_nat,
  norm_cast,
  norm_num,
},
apply submodule.ext,
rintros,
split,
{
  rintros,
  rw submodule.mem_span_singleton,
  use (x * (π^(Inf Q))⁻¹),
  {
    dunfold val_ring,
    simp,
    rw mul,
    by_cases x = 0,
    {
      rw h,
      simp,
    },
    rw with_top.add_le_happens (v(π^(Inf Q))),
    {
      norm_num,
      rw add_left_comm,
      rw val_inv,
      simp,
      rw g,
      have f' : ∃ m : ℕ, v(x:K) = ↑m,
      {
        apply val_is_nat,
        use hπ,
        exact h,
      },
      cases f' with m f',
      rw f',
      rw <-with_top.coe_nat,
      rw <-with_top.coe_nat,
      norm_cast,
      have h' : m ∈ Q,
      {
        split,
        simp,
        split,
        use a,
        use [eq.symm f'],
      },
      by { rw [nat.Inf_def ⟨m, h'⟩], exact nat.find_min' ⟨m, h'⟩ h' },
      assumption,
    },
    rw g,
    exact with_top.nat_ne_top _,
  },
  {
    tidy,
    assoc_rw inv_mul_cancel nz,
    simp,
  },
},
{
  rw submodule.mem_span,
  rintros,
  specialize a S,
  apply a,
  have f : ∃ z ∈ S, v(z : K) = ↑(Inf Q),
  {
    have f' : ∃ x ∈ S, v(x : K) ≠ ⊤,
    {
      contrapose h,
      simp at h,
      simp,
      apply ideal.ext,
      rintros,
      simp only [submodule.mem_bot],
      split,
      rintros,
      specialize h x_1,
      simp at h,
      have q : v(x_1 : K) = ⊤,
      apply h,
      exact a_1,
      rw non_zero at q,
      exact subtype.ext q,
      rintros,
      rw a_1,
      simp,
    },
    have p : Inf Q ∈ Q,
    {
      apply nat.Inf_mem,
      contrapose h,
      simp,
      by_contradiction,
      cases f' with x' f',
      have f_1 : ∃ m : ℕ, v(x':K) = ↑(m),
      {
        apply val_is_nat,
        exact hπ,
        cases f',
        contrapose f'_h,
        simp,
        rw non_zero,
        simp at f'_h,
        rw f'_h,
        simp,
      },
      cases f_1 with m' f_1,
      have g' : m' ∈ Q,
      {
        simp,
        use x',
        simp,
        split,
        cases f',
        assumption,
        exact eq.symm f_1,
      },
      apply h,
      use m',
      apply g',
    },
    simp at p,
    cases p with z p,
    cases p,
    use z,
    cases p_left,
    assumption,
    split,
    cases p_left,
    assumption,
    simp,
    exact eq.symm p_right,
  },
  cases f with z f,
  rw <-g at f,
  simp at f,
  cases f,
  rw val_eq_iff_asso at f_right,
  {
    cases f_right with w f_1,
    cases f_1 with f_1 f_2,
    cases f_2 with f_2 f_3,
    rw set.singleton_subset_iff,
    simp only [submodule.mem_coe],
    simp_rw [← f_3],
    change z * ⟨w,f_1⟩ ∈ S,
    apply ideal.mul_mem_right S f_left,
  },
  simp,
  {
    unfold val_ring,
    simp,
    rw g,
    rw <-with_top.coe_nat,
    norm_cast,
    simp,
  },
  {
    rw g at f_right,
    contrapose f_right,
    simp at f_right,
    rw <-non_zero at f_right,
    rw f_right,
    simp,
  },
  {
    exact nz,
  },
},
recover,
end

end discrete_valuation_field

end discrete_valuation_ring
#exit
import set_theory.cardinal

universes u v

example : cardinal.lift.{u v} = cardinal.lift.{u (max u v)} :=
funext $ λ x, quotient.induction_on x
  (λ x, quotient.sound ⟨⟨λ ⟨x⟩, ⟨x⟩, λ ⟨x⟩, ⟨x⟩, λ ⟨_,⟩, rfl, λ ⟨_⟩, rfl⟩⟩)


import tactic.rcases

lemma L1 : forall (n m: ℕ) (p : ℕ → Prop), (p n ∧ ∃ (u:ℕ), p u ∧ p m) ∨ (¬p n ∧ p m) → n = m :=
begin
  intros n m p H,
  rcases H with ⟨H1, u, H2, H3⟩ | ⟨H1, H2⟩,

end

#exit

import data.polynomial

example {K L M : Type*} [field K] [field L] [field M]
  (i : K →+* L) (j : L →+* M) (f : polynomial K)
  (h : ∃ x, f.eval₂ i x)

#exit

import ring_theory.eisenstein_criterion

variables {R : Type*} [integral_domain R]

lemma dvd_mul_prime {x a p : R} (hp : prime p) : x ∣ a * p → x ∣ a ∨ p ∣ x :=
λ ⟨y, hy⟩, (hp.div_or_div ⟨a, hy.symm.trans (mul_comm _ _)⟩).elim
  or.inr
  begin
    rintros ⟨b, rfl⟩,
    rw [mul_left_comm, mul_comm, domain.mul_right_inj hp.ne_zero] at hy,
    rw [hy],
    exact or.inl (dvd_mul_right _ _)
  end
#print well_founded.m
in
lemma left_dvd_or_dvd_right_of_dvd_prime_mul {a : R} :
  ∀ {b p : R}, prime p → a ∣ p * b → p ∣ a ∨ a ∣ b :=
begin
  rintros b p hp ⟨c, hc⟩,
  rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with h | ⟨x, rfl⟩,
  { exact or.inl h },
  { rw [mul_left_comm, domain.mul_right_inj hp.ne_zero] at hc,
    exact or.inr (hc.symm ▸ dvd_mul_right _ _) }
end

#exit
import data.nat.basic data.quot

inductive rel : ℕ ⊕ ℕ →  ℕ ⊕ ℕ → Prop
| zero : rel (sum.inl 0) (sum.inr 0)
| refl : ∀ x, rel x x
| symm : ∀ {x y}, rel x y → rel y x
| trans : ∀ {x y z}, rel x y → rel y z → rel x z

attribute [refl] rel.refl
attribute [symm] rel.symm
attribute [trans] rel.trans


instance srel : setoid (ℕ ⊕ ℕ) :=
{ r := rel,
  iseqv := ⟨rel.refl, @rel.symm, @rel.trans⟩ }

def int' := quotient srel



#exit
import data.finset data.fintype.card

example (n m : ℕ) (hn : n ≠ 0) (hm : n ≤ m) : m ≠ 0 := λ h, by simp * at *
#print discrete
universe u
variables {α : Type u} [add_comm_monoid α]

open_locale big_operators
ʗ∁ C
example {u : Type*} {v : Type*} [fintype u] [fintype v] (f : u × v -> α) :
  ∑ (i : u), ∑ (j : v), f (i, j) = ∑ (p : u × v), f p :=
begin
  rw <-finset.sum_product,
  repeat { rw finset.univ },
  sorry,
end
#exit

import data.set.finite tactic

variables {α : Type*} (r : α → α → Prop)

lemma well_founded_of_finite [is_irrefl α r] [is_trans α r]
  (h : ∀ a₀, set.finite {a | r a a₀}) : well_founded r :=
⟨λ a₀, acc.intro _ (λ b hb, begin
  cases h a₀ with fint,
  refine @well_founded.fix {a | r a a₀} (λ b, acc r b) (λ x y : {a | r a a₀}, r x y)
    (@fintype.well_founded_of_trans_of_irrefl _ fint
      (λ x y : {a | r a a₀}, r x y) ⟨λ x y z h₁ h₂, trans h₁ h₂⟩
      ⟨λ x, irrefl x⟩) _ ⟨b, hb⟩,
  rintros ⟨b, hb⟩ ih,
  exact acc.intro _ (λ y hy, ih ⟨y, trans hy hb⟩ hy)
end)⟩

#exit

import algebra.group_power

theorem pow_eq_zero_1 {R : Type} [domain R] {r : R} {n : ℕ} : r ^ (n + 1) = 0 → r = 0
:= begin
  rw (show r ^ (n + 1) = r ^ n * r,
      by {
           sorry, }),
  sorry,
end



theorem pow_eq_zero_2  {R : Type} [domain R] {r : R} {n : ℕ} : r ^ (n + 1) = 0 → r = 0
:= pow_eq_zero  -- it's in mathlib

import tactic

def five : ℕ := 5

meta def tac : tactic unit := tactic.focus1 `[tactic.intro1, tactic.applyc `five]

run_cmd add_interactive [`tac]

def C : ℕ → ℕ :=
by tac
#print C

inductive palindrome {α : Type} : list α → Prop
| nil  : palindrome []
| singleton : \al palindrom []


def reverse {α : Type} : list α → list α
| [] := []
| (x :: xs) := reverse xs ++ [x]




end

#exit

import group_theory.subgroup ring_theory.ideal_operations

--attribute [irreducible] subgroup.normal

example {R : Type} [comm_ring R] (P : ideal R) (hP : P.is_prime) : P.is_prime :=
by apply_instance

example {G : Type} [group G] (N : subgroup G) (hN : N.normal) : N.normal :=
by apply_instance

#print subgroup.normal


#exit
import ring_theory.ideal_operations data.polynomial ring_theory.ideals tactic.apply_fun

open polynomial ideal.quotient

open_locale classical

variables {R : Type*} [integral_domain R]

open polynomial ideal.quotient

open finset

open_locale big_operators

lemma mul_eq_mul_prime_prod {α : Type*} [decidable_eq α] {x y a : R} {s : finset α}
  {p : α → R} (hp : ∀ i ∈ s, prime (p i)) (hx : x * y = a * s.prod p) :
  ∃ t u b c, t ∪ u = s ∧ disjoint t u ∧ b * c = a ∧
    x = b * t.prod p ∧ y = c * u.prod p :=
begin
  induction s using finset.induction with i s his ih generalizing x y a,
  { exact ⟨∅, ∅, x, y, by simp [hx]⟩ },
  { rw [prod_insert his, ← mul_assoc] at hx,
    have hpi : prime (p i), { exact hp i (mem_insert_self _ _) },
    rcases ih (λ i hi, hp i (mem_insert_of_mem hi)) hx with
      ⟨t, u, b, c, htus, htu, hbc, rfl, rfl⟩,
    have hpibc : p i ∣ b ∨ p i ∣ c,
      from hpi.div_or_div ⟨a, by rw [hbc, mul_comm]⟩,
    have hit : i ∉ t, from λ hit, his (htus ▸ mem_union_left _ hit),
    have hiu : i ∉ u, from λ hiu, his (htus ▸ mem_union_right _ hiu),
    rcases hpibc with ⟨d, rfl⟩ | ⟨d, rfl⟩,
    { rw [mul_assoc, mul_comm a, domain.mul_right_inj hpi.ne_zero] at hbc,
      exact ⟨insert i t, u, d, c, by rw [insert_union, htus],
        disjoint_insert_left.2 ⟨hiu, htu⟩,
          by simp [← hbc, prod_insert hit, mul_assoc, mul_comm, mul_left_comm]⟩ },
    { rw [← mul_assoc, mul_right_comm b, domain.mul_left_inj hpi.ne_zero] at hbc,
      exact ⟨t, insert i u, b, d, by rw [union_insert, htus],
        disjoint_insert_right.2 ⟨hit, htu⟩,
          by simp [← hbc, prod_insert hiu, mul_assoc, mul_comm, mul_left_comm]⟩ } }
end

lemma mul_eq_mul_prime_pow {x y a p : R} {n : ℕ} (hp : prime p) (hx : x * y = a * p ^ n) :
  ∃ i j b c, i + j = n ∧ b * c = a ∧ x = b * p ^ i ∧ y = c * p ^ j :=
begin
  rcases mul_eq_mul_prime_prod (λ _ _, hp)
    (show x * y = a * (range n).prod (λ _, p), by simpa) with
    ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩,
  exact ⟨t.card, u.card, b, c, by rw [← card_disjoint_union htu, htus, card_range], by simp⟩,
end

lemma eisenstein {f : polynomial R} {P : ideal R} (hP : P.is_prime)
  (hfl : f.leading_coeff ∉ P)
  (hfP : ∀ n : ℕ, ↑n < degree f → f.coeff n ∈ P)
  (hfd0 : 0 < degree f) (h0 : f.coeff 0 ∉ P^2)
  (hu : ∀ x : R, C x ∣ f → is_unit x) : irreducible f :=
have hf0 : f ≠ 0, from λ _, by simp * at *,
have hf : f.map (mk_hom P) =
    C (mk_hom P (leading_coeff f)) * X ^ nat_degree f,
  from polynomial.ext (λ n, begin
    rcases lt_trichotomy ↑n (degree f) with h | h | h,
    { erw [coeff_map, ← mk_eq_mk_hom, eq_zero_iff_mem.2 (hfP n h),
        coeff_C_mul, coeff_X_pow, if_neg, mul_zero],
      rintro rfl, exact not_lt_of_ge degree_le_nat_degree h },
    { have : nat_degree f = n, from nat_degree_eq_of_degree_eq_some h.symm,
      rw [coeff_C_mul, coeff_X_pow, if_pos this.symm, mul_one, leading_coeff, this, coeff_map] },
    { rw [coeff_eq_zero_of_degree_lt, coeff_eq_zero_of_degree_lt],
      { refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) _,
        rwa ← degree_eq_nat_degree hf0 },
      { exact lt_of_le_of_lt (degree_map_le _) h } }
  end),
have hfd0 : 0 < f.nat_degree, from with_bot.coe_lt_coe.1
  (lt_of_lt_of_le hfd0 degree_le_nat_degree),
⟨mt degree_eq_zero_of_is_unit (λ h, by simp [*, lt_irrefl] at *),
begin
  rintros p q rfl,
  rw [map_mul] at hf,
  have : map (mk_hom P) p ∣ C (mk_hom P (p * q).leading_coeff) * X ^ (p * q).nat_degree,
    from ⟨map (mk_hom P) q, hf.symm⟩,
  rcases mul_eq_mul_prime_pow (show prime (X : polynomial (ideal.quotient P)),
    from prime_of_degree_eq_one_of_monic degree_X monic_X) hf with
      ⟨m, n, b, c, hmnd, hbc, hp, hq⟩,
  have hmn : 0 < m → 0 < n → false,
  { assume hm0 hn0,
    have hp0 : p.eval 0 ∈ P,
    { rw [← coeff_zero_eq_eval_zero, ← eq_zero_iff_mem, mk_eq_mk_hom, ← coeff_map],
      simp [hp, coeff_zero_eq_eval_zero, zero_pow hm0] },
    have hq0 : q.eval 0 ∈ P,
    { rw [← coeff_zero_eq_eval_zero, ← eq_zero_iff_mem, mk_eq_mk_hom, ← coeff_map],
      simp [hq, coeff_zero_eq_eval_zero, zero_pow hn0] },
    apply h0,
    rw [coeff_zero_eq_eval_zero, eval_mul, pow_two],
    exact ideal.mul_mem_mul hp0 hq0 },
  have hpql0 : (mk_hom P) (p * q).leading_coeff ≠ 0,
  { rwa [← mk_eq_mk_hom, ne.def, eq_zero_iff_mem] },
  have hp0 : p ≠ 0, from λ h, by simp * at *,
  have hq0 : q ≠ 0, from λ h, by simp * at *,
  have hmn0 : m = 0 ∨ n = 0,
  { rwa [nat.pos_iff_ne_zero, nat.pos_iff_ne_zero, imp_false, not_not,
      ← or_iff_not_imp_left] at hmn },
  have hbc0 : degree b = 0 ∧ degree c = 0,
  { apply_fun degree at hbc,
    rwa [degree_C hpql0, degree_mul_eq, nat.with_bot.add_eq_zero_iff] at hbc },
  have hmp : m ≤ nat_degree p,
    from with_bot.coe_le_coe.1
      (calc ↑m = degree (p.map (mk_hom P)) : by simp [hp, hbc0.1]
         ... ≤ degree p : degree_map_le _
         ... ≤ nat_degree p : degree_le_nat_degree),
  have hmp : n ≤ nat_degree q,
    from with_bot.coe_le_coe.1
      (calc ↑n = degree (q.map (mk_hom P)) : by simp [hq, hbc0.2]
         ... ≤ degree q : degree_map_le _
         ... ≤ nat_degree q : degree_le_nat_degree),
  have hpmqn : p.nat_degree = m ∧ q.nat_degree = n,
  { rw [nat_degree_mul_eq hp0 hq0] at hmnd, omega },
  rcases hmn0 with rfl | rfl,
  { left,
    rw [eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.1),
      is_unit_C],
    refine hu _ _,
    rw [← eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.1)],
    exact dvd_mul_right _ _ },
  { right,
    rw [eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.2),
      is_unit_C],
    refine hu _ _,
    rw [← eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.2)],
    exact dvd_mul_left _ _ }
end⟩

#print axioms eisenstein

#exit
import algebra.ring
universe u
variables {R : Type} [comm_ring R] (M : submonoid R)
set_option pp.all true
#print comm_ring.zero_add
instance : comm_monoid (submonoid.localization M) :=
(submonoid.localization.r M).comm_monoid

@[elab_as_eliminator]
protected def lift_on₂ {α : Type*} [monoid α] {β} {c : con α } (q r : c.quotient) (f : α → α → β)
  (h : ∀ a₁ a₂ b₁ b₂, c a₁ b₁ → c a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β := quotient.lift_on₂' q r f h

def submonoid.localization.mk : R → M → submonoid.localization M :=
λ x y, (submonoid.localization.r M).mk' (x, y)

theorem r_of_eq {x y : R × M} (h : y.1 * x.2 = x.1 * y.2) :
  submonoid.localization.r M x y :=
submonoid.localization.r_iff_exists.2 ⟨1, by rw h⟩

instance : has_zero (submonoid.localization M) :=
⟨submonoid.localization.mk M 0 1⟩

instance : has_add (submonoid.localization M) :=
⟨λ z w, lift_on₂ z w
  (λ x y : R × M, submonoid.localization.mk M ((x.2 : R) * y.1 + y.2 * x.1) (x.2 * y.2)) $
λ r1 r2 r3 r4 h1 h2, (con.eq _).2
begin
  rw submonoid.localization.r_eq_r' at h1 h2 ⊢,
  cases h1 with t₅ ht₅,
  cases h2 with t₆ ht₆,
  use t₆ * t₅,
  calc ((r1.2 : R) * r2.1 + r2.2 * r1.1) * (r3.2 * r4.2) * (t₆ * t₅) =
      (r2.1 * r4.2 * t₆) * (r1.2 * r3.2 * t₅) + (r1.1 * r3.2 * t₅) * (r2.2 * r4.2 * t₆) : by ring
      ... = (r3.2 * r4.1 + r4.2 * r3.1) * (r1.2 * r2.2) * (t₆ * t₅) : by rw [ht₆, ht₅]; ring
end⟩

instance : has_neg (submonoid.localization M) :=
⟨λ z, con.lift_on z (λ x : R × M, submonoid.localization.mk M (-x.1) x.2) $
  λ r1 r2 h, (con.eq _).2
begin
  rw submonoid.localization.r_eq_r' at h ⊢,
  cases h with t ht,
  use t,
  rw [neg_mul_eq_neg_mul_symm, neg_mul_eq_neg_mul_symm, ht],
  ring,
end⟩
instance : add_semigroup (submonoid.localization M) := by apply_instance


set_option pp.all true

#print comm_ring.zero_add

@[instance]lemma C : comm_ring (submonoid.localization M) :=
{ zero := (0 : submonoid.localization M),
  one  := (1 : submonoid.localization M),
  add  := (+),
  mul  := (*),
  zero_add       := λ y : submonoid.localization M, quotient.induction_on' y _,
  add_zero       := λ y : submonoid.localization M, quotient.induction_on' y _,
  add_assoc      := λ m n k : submonoid.localization M,
    quotient.induction_on₃' m n k _,
  neg            := has_neg.neg,
  add_left_neg   := λ y : submonoid.localization M, quotient.induction_on' y _,
  add_comm       := λ y z : submonoid.localization M, quotient.induction_on₂' z y _,
  left_distrib   := λ m n k : submonoid.localization M, quotient.induction_on₃' m n k _,
  right_distrib  := λ m n k : submonoid.localization M, quotient.induction_on₃' m n k _,
   ..submonoid.localization.comm_monoid M }
--   { intros,
--      refine quotient.sound (r_of_eq M _),
--      simp only [prod.snd_mul, prod.fst_mul, submonoid.coe_mul],
--      ring }
-- end


example (y m n k : submonoid.localization M) : Prop := @eq.{1} M.localization
    (@has_add.add.{0} M.localization
       (@add_semigroup.to_has_add.{0} M.localization
          (@add_semigroup.mk.{0} M.localization
             (@has_add.add.{0} M.localization (@submonoid.localization.has_add R _inst_1 M))
             _
            --  (λ (m n k : M.localization),
            --     @quotient.induction_on₃'.{1 1 1}
            --       (prod.{0 0} R
            --          (@coe_sort.{1 2}
            --             (@submonoid.{0} R
            --                (@comm_monoid.to_monoid.{0} R
            --                   (@comm_semiring.to_comm_monoid.{0} R (@comm_ring.to_comm_semiring.{0} R _inst_1))))
            --             (@submonoid.has_coe_to_sort.{0} R
            --                (@comm_monoid.to_monoid.{0} R
            --                   (@comm_semiring.to_comm_monoid.{0} R (@comm_ring.to_comm_semiring.{0} R _inst_1))))
            --             M))
            --       (prod.{0 0} R
            --          (@coe_sort.{1 2}
            --             (@submonoid.{0} R
            --                (@comm_monoid.to_monoid.{0} R
            --                   (@comm_semiring.to_comm_monoid.{0} R (@comm_ring.to_comm_semiring.{0} R _inst_1))))
            --             (@submonoid.has_coe_to_sort.{0} R
            --                (@comm_monoid.to_monoid.{0} R
            --                   (@comm_semiring.to_comm_monoid.{0} R (@comm_ring.to_comm_semiring.{0} R _inst_1))))
            --             M))
            --       (prod.{0 0} R
            --          (@coe_sort.{1 2}
            --             (@submonoid.{0} R
            --                (@comm_monoid.to_monoid.{0} R
            --                   (@comm_semiring.to_comm_monoid.{0} R (@comm_ring.to_comm_semiring.{0} R _inst_1))))
            --             (@submonoid.has_coe_to_sort.{0} R
            --                (@comm_monoid.to_monoid.{0} R
            --                   (@comm_semiring.to_comm_monoid.{0} R (@comm_ring.to_comm_semiring.{0} R _inst_1))))
            --             M))
            --       (@submonoid.localization.r.{0} R
            --          (@comm_semiring.to_comm_monoid.{0} R (@comm_ring.to_comm_semiring.{0} R _inst_1))
            --          M).to_setoid
            --       (@submonoid.localization.r.{0} R
            --          (@comm_semiring.to_comm_monoid.{0} R (@comm_ring.to_comm_semiring.{0} R _inst_1))
            --          M).to_setoid
            --       (@submonoid.localization.r.{0} R
            --          (@comm_semiring.to_comm_monoid.{0} R (@comm_ring.to_comm_semiring.{0} R _inst_1))
            --          M).to_setoid
            --       (λ (_x _x_1 _x_2 : M.localization),
            --          @eq.{1} M.localization
            --            (@has_add.add.{0} M.localization
            --               (@has_add.mk.{0} M.localization
            --                  (@has_add.add.{0} M.localization (@submonoid.localization.has_add R _inst_1 M)))
            --               (@has_add.add.{0} M.localization
            --                  (@has_add.mk.{0} M.localization
            --                     (@has_add.add.{0} M.localization (@submonoid.localization.has_add R _inst_1 M)))
            --                  _x
            --                  _x_1)
            --               _x_2)
            --            (@has_add.add.{0} M.localization
            --               (@has_add.mk.{0} M.localization
            --                  (@has_add.add.{0} M.localization (@submonoid.localization.has_add R _inst_1 M)))
            --               _x
            --               (@has_add.add.{0} M.localization
            --                  (@has_add.mk.{0} M.localization
            --                     (@has_add.add.{0} M.localization (@submonoid.localization.has_add R _inst_1 M)))
            --                  _x_1
            --                  _x_2)))
            --       m
            --       n
            --       k
            --     _)
            )) _
      --  (@has_zero.zero.{0} M.localization
      --     (@has_zero.mk.{0} M.localization
      --        (@has_zero.zero.{0} M.localization (@submonoid.localization.has_zero R _inst_1 M))))
       y
       )
    y
#exit
import category_theory.limits.shapes.pullbacks

open category_theory
open category_theory.limits

universes v u

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
#print is_colimit
def pushout_of_epi {X Y : C} (f : X ⟶ Y) [epi f] :
  is_colimit (pushout_cocone.mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f) :=
{ desc := λ s, s.ι.app walking_span.left,
  fac' := λ s j, option.cases_on j
    (by { tidy, convert s.w walking_span.hom.fst })




  (λ j, walking_pair.cases_on j (by tidy) begin
    tidy,

  end) }

theorem epi_of_pushout {X Y : C} (f : X ⟶ Y)
  (is_colim : is_colimit (pushout_cocone.mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f)) : epi f := sorry

#exit
import data.fintype.basic


#exit
import algebra.ring tactic

def add : Π l₁ l₂ : list nat, list nat
| []      l₂      := l₂
| l₁      []      := l₁
| (a::l₁) (b::l₂) :=
if h : b < a then b :: add (a :: l₁) l₂
else a :: add l₁ (b :: l₂)

#exit
namespace tactic

meta def protect (n : name) : tactic unit :=
do env ← get_env, set_env $ env.mk_protected n

end tactic

namespace nat

private lemma X : true := trivial

run_cmd tactic.protect `nat.X

example : true := X

end nat

open category_theory

instance A : is_semiring_hom (coe : ℤ → ℚ) :=
by refine_struct { .. }; simp

@[reducible] def icast : ℤ →+* ℚ := ring_hom.of coe

lemma unique_hom {R : Type*} [ring R] (f g : ℚ →+* R) : f = g :=
begin
  ext,
  refine rat.num_denom_cases_on x (λ n d hd0 _, _),
  have hd0 : (d : ℚ) ≠ 0, { simpa [nat.pos_iff_ne_zero] using hd0 },
  have hf : ∀ n : ℤ, f n = n, from λ _, (f.comp icast).eq_int_cast _,
  have hg : ∀ n : ℤ, g n = n, from λ _, (g.comp icast).eq_int_cast _,
  have : is_unit ((d  : ℤ) : R),
    from ⟨⟨f d, f (1 / d), by rw [← ring_hom.map_mul, mul_div_cancel' _ hd0, f.map_one],
      by rw [← ring_hom.map_mul, div_mul_cancel _ hd0, f.map_one]⟩,
    by simp [hf]⟩ ,
  rw [rat.mk_eq_div, div_eq_mul_inv, ring_hom.map_mul, ring_hom.map_mul, hf, hg,
    ← this.mul_left_inj],
  conv_lhs { rw ← hf d },
  rw [← hg d, mul_assoc, mul_assoc, ← f.map_mul, ← g.map_mul, int.cast_coe_nat,
    inv_mul_cancel hd0],
  simp
end

theorem mono_epi_not_iso : ∃ (A B : Ring.{0}) (f : A ⟶ B),
  mono.{0} f ∧ epi.{0} f ∧ (is_iso.{0} f → false) :=
⟨Ring.of ℤ, Ring.of ℚ, icast,
  ⟨begin
    intros,
    ext,
    tidy,
    rw [function.funext_iff] at h_1,
    erw [← @int.cast_inj ℚ],
    exact h_1 _
  end⟩,
  ⟨λ _ _ _ _,  unique_hom _ _⟩,
  λ h,
    have (2 : ℤ) ∣ 1,
      from ⟨(h.inv : ℚ →+* ℤ) (show ℚ, from (1 : ℚ) / 2),
        have (2 : ℤ) = (h.inv : ℚ →+* ℤ) (2 : ℚ), by simp [bit0],
        begin
          rw [this, ← ring_hom.map_mul],
          norm_num,
        end⟩,
    absurd this (by norm_num)⟩

#exit
import ring_theory.ideal_operations data.polynomial ring_theory.ideals tactic
section comm_ring
variables {R : Type*} {S : Type*} [comm_ring R] [comm_ring S]

open polynomial ideal.quotient

open_locale classical

lemma thingy {R : Type*} [comm_ring R] (I : ideal R)
  {a : R} (hab : a ∉ I^2) (hu : ∀ u ∉ I, u ∣ a → is_unit u)
  (ha : ¬ is_unit a) : irreducible a :=
⟨ha, λ x y hxy,
have hxPyP : x ∈ I → y ∈ I → false,
  from λ hxP hyP, hab (by rw [hxy, pow_two]; exact ideal.mul_mem_mul hxP hyP),
(show x ∉ I ∨ y ∉ I, by rwa [or_iff_not_imp_left, not_not]).elim
  (λ hx, or.inl (hu x hx $ by simp [hxy]))
  (λ hy, or.inr (hu y hy $ by simp [hxy]))⟩

lemma thingy2 {R : Type*} [comm_ring R] (I : ideal R)
  {a : R} (hab : a ∉ I^2) (hu : ∀ x ∉ I, x ∣ a → ∃ u, 1 - u * x ∈ I)
  (ha : ¬ is_unit a) : irreducible a :=
⟨ha, λ x y hxy,
have hxPyP : x ∈ I → y ∈ I → false,
  from λ hxP hyP, hab (by rw [hxy, pow_two]; exact ideal.mul_mem_mul hxP hyP),
(show x ∉ I ∨ y ∉ I, by rwa [or_iff_not_imp_left, not_not]).elim
  (λ hx, begin
    cases hu x hx (by simp [hxy]) with u hu,


  end)
  (λ hy, or.inr (hu y hy $ by simp [hxy]))⟩

lemma ideal.sup_pow_two {I J : ideal R} : (I ⊔ J) ^ 2 = I ^ 2 ⊔ I * J ⊔ J ^ 2 :=
by simp [ideal.sup_mul, ideal.mul_sup, mul_comm, pow_two, sup_assoc]


#print ring_hom.of
lemma eisenstein {R : Type*} [integral_domain R] {f : polynomial R}
  {P : ideal R} --(hP : P.is_prime) --(hfl : f.leading_coeff ∉ P)
  --(hfP : ∀ n : ℕ, ↑n < degree f → f.coeff n ∈ P)
  --(hfd0 : 0 < degree f)
  (h0 : f.coeff 0 ∉ P^2)
  (hu : ∀ x : R, C x ∣ f → is_unit x) : irreducible f :=
have eq_id : (ring_hom.of (eval (0 : R))).comp (ring_hom.of C) = ring_hom.id _,
  by ext; simp,
have h_ker : ideal.span {(X : polynomial R)} ≤ (ring_hom.of (eval (0 : R))).ker,
  from ideal.span_le.2 (λ _, by simp [ring_hom.mem_ker] {contextual := tt}),
thingy (P.map (ring_hom.of C) ⊔ ideal.span {X})
  (λ hf, h0 $
    begin
      have := @ideal.mem_map_of_mem _ _ _ _ (ring_hom.of (eval 0)) _ _ hf,
      rwa [pow_two, ideal.map_mul, ideal.map_sup, ideal.map_map, eq_id, ideal.map_id,
        map_eq_bot_iff_le_ker.1 h_ker, sup_bot_eq, ring_hom.coe_of,
        ← coeff_zero_eq_eval_zero, ← pow_two] at this
    end)
  begin
    assume x hx,


  end
  _

example {R : Type*} [comm_ring R] {P Q : ideal R} (hP : P.is_prime) (hQ : Q.is_prime)
  (hPQ : (P ⊔ Q).is_prime) {a : R} (ha : a ∈ P ⊔ Q^2) (hab : a ∉ P ^ 2 ⊔ Q) (haP : a ∉ P)
  (hu : ∀ u ∉ Q, u ∣ a → is_unit u) : irreducible a :=
⟨sorry, λ x y hxy,
have hxQyQ : x ∈ P ⊔ Q → y ∈ P ⊔ Q → false,
  from λ hxQ hyQ, hab begin
    have haPQ: a ∈ ((P ⊔ Q) * (P ⊔ Q)),
      from hxy.symm ▸ (ideal.mul_mem_mul hxQ hyQ),
    have : ((P ⊔ Q) * (P ⊔ Q)) ≤ P ^ 2 ⊔ Q,
      { rw [ideal.mul_sup, ideal.sup_mul, ideal.sup_mul, sup_assoc,
          ← @sup_assoc  _ _ (Q * P), mul_comm Q P, sup_idem, ← ideal.sup_mul, pow_two],
        exact sup_le_sup (le_refl _) ideal.mul_le_left },
    exact this haPQ
  end,

begin
  subst a,


end⟩
end comm_ring

variables {R : Type*} [integral_domain R]

open polynomial ideal.quotient

@[simp] lemma nat.with_bot.coe_nonneg {n : ℕ} : 0 ≤ (n : with_bot ℕ) :=
by rw [← with_bot.coe_zero, with_bot.coe_le_coe]; exact nat.zero_le _

@[simp] lemma nat.with_bot.lt_zero (n : with_bot ℕ) : n < 0 ↔ n = ⊥ :=
option.cases_on n dec_trivial (λ n, iff_of_false
  (by simp [with_bot.some_eq_coe]) (λ h, option.no_confusion h))

example (n : with_bot ℕ) : n.lt_zero

lemma degree_nonneg_iff_ne_zero {R : Type*} [comm_semiring R]
  {f : polynomial R} : 0 ≤ degree f ↔ f ≠ 0 :=
⟨λ h0f hf0, absurd h0f (by rw [hf0, degree_zero]; exact dec_trivial),
  λ hf0, le_of_not_gt (λ h, by simp [gt, degree_eq_bot, *] at *)⟩

lemma nat_degree_eq_zero_iff_degree_le_zero {R : Type*} [comm_semiring R]
  {p : polynomial R} : p.nat_degree = 0 ↔ p.degree ≤ 0 :=
if hp0 : p = 0 then by simp [hp0]
else by rw [degree_eq_nat_degree hp0, ← with_bot.coe_zero, with_bot.coe_le_coe,
  nat.le_zero_iff]

lemma eq_one_of_is_unit_of_monic {R : Type*} [comm_semiring R]
  {p : polynomial R} (hm : monic p) (hpu : is_unit p) : p = 1 :=
have degree p ≤ 0,
  from calc degree p ≤ degree (1 : polynomial R) :
    let ⟨u, hu⟩ := is_unit_iff_dvd_one.1 hpu in
    if hu0 : u = 0
    then begin
        rw [hu0, mul_zero] at hu,
        rw [← mul_one p, hu, mul_zero],
        simp
      end
    else have p.leading_coeff * u.leading_coeff ≠ 0,
        by rw [hm.leading_coeff, one_mul, ne.def, leading_coeff_eq_zero];
          exact hu0,
      by rw [hu, degree_mul_eq' this];
        exact le_add_of_nonneg_right' (degree_nonneg_iff_ne_zero.2 hu0)
  ... ≤ 0 : degree_one_le,
by rw [eq_C_of_degree_le_zero this, ← nat_degree_eq_zero_iff_degree_le_zero.2 this,
    ← leading_coeff, hm.leading_coeff, C_1]

open finset

lemma dvd_mul_prime {x a p : R} (hp : prime p) : x ∣ a * p → x ∣ a ∨ p ∣ x :=
λ ⟨y, hy⟩, (hp.div_or_div ⟨a, hy.symm.trans (mul_comm _ _)⟩).elim
  or.inr
  begin
    rintros ⟨b, rfl⟩,
    rw [mul_left_comm, mul_comm, domain.mul_right_inj hp.ne_zero] at hy,
    rw [hy],
    exact or.inl (dvd_mul_right _ _)
  end

lemma dvd_mul_prime_prod {α : Type*} {x a : R} {s : finset α}
  {p : α → R} (hp : ∀ i ∈ s, prime (p i)) (hx : x ∣ a * s.prod p) :
  ∃ t b, t ⊆ s ∧ b ∣ a ∧ x = b * t.prod p :=
begin
  classical,
  rcases hx with ⟨y, hy⟩,
  induction s using finset.induction with i s his ih generalizing x y a,
  { exact ⟨∅, x, finset.subset.refl _, ⟨y, hy ▸ by simp⟩, by simp⟩ },
  { rw [prod_insert his, ← mul_assoc] at hy,
    have hpi : prime (p i), { exact hp i (mem_insert_self _ _) },
    rcases ih (λ i hi, hp i (mem_insert_of_mem hi)) _ hy with ⟨t, b, hts, hb, rfl⟩,
    rcases dvd_mul_prime hpi hb with hba | ⟨c, rfl⟩,
    { exact ⟨t, b, trans hts (subset_insert _ _), hba, rfl⟩ },
    { exact ⟨insert i t, c, insert_subset_insert _ hts,
        by rwa [mul_comm, mul_dvd_mul_iff_right hpi.ne_zero] at hb,
        by rw [prod_insert (mt (λ x, hts x) his), mul_left_comm, mul_assoc]⟩, } }
end

lemma mul_eq_mul_prime_prod {α : Type*} [decidable_eq α] {x y a : R} {s : finset α}
  {p : α → R} (hp : ∀ i ∈ s, prime (p i)) (hx : x * y = a * s.prod p) :
  ∃ t u b c, t ∪ u = s ∧ disjoint t u ∧ b * c = a ∧
    x = b * t.prod p ∧ y = c * u.prod p :=
begin
  induction s using finset.induction with i s his ih generalizing x y a,
  { exact ⟨∅, ∅, x, y, by simp [hx]⟩ },
  { rw [prod_insert his, ← mul_assoc] at hx,
    have hpi : prime (p i), { exact hp i (mem_insert_self _ _) },
    rcases ih (λ i hi, hp i (mem_insert_of_mem hi)) hx with
      ⟨t, u, b, c, htus, htu, hbc, rfl, rfl⟩,
    have hpibc : p i ∣ b ∨ p i ∣ c,
      from hpi.div_or_div ⟨a, by rw [hbc, mul_comm]⟩,
    have hit : i ∉ t, from λ hit, his (htus ▸ mem_union_left _ hit),
    have hiu : i ∉ u, from λ hiu, his (htus ▸ mem_union_right _ hiu),
    rcases hpibc with ⟨d, rfl⟩ | ⟨d, rfl⟩,
    { rw [mul_assoc, mul_comm a, domain.mul_right_inj hpi.ne_zero] at hbc,
      exact ⟨insert i t, u, d, c, by rw [insert_union, htus],
        disjoint_insert_left.2 ⟨hiu, htu⟩,
          by simp [← hbc, prod_insert hit, mul_assoc, mul_comm, mul_left_comm]⟩ },
    { rw [← mul_assoc, mul_right_comm b, domain.mul_left_inj hpi.ne_zero] at hbc,
      exact ⟨t, insert i u, b, d, by rw [union_insert, htus],
        disjoint_insert_right.2 ⟨hit, htu⟩,
          by simp [← hbc, prod_insert hiu, mul_assoc, mul_comm, mul_left_comm]⟩ } }
end

lemma mul_eq_mul_prime_pow {x y a p : R} {n : ℕ} (hp : prime p) (hx : x * y = a * p ^ n) :
  ∃ i j b c, i + j = n ∧ b * c = a ∧ x = b * p ^ i ∧ y = c * p ^ j :=
begin
  rcases mul_eq_mul_prime_prod (λ _ _, hp)
    (show x * y = a * (range n).prod (λ _, p), by simpa) with
    ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩,
  exact ⟨t.card, u.card, b, c, by rw [← card_disjoint_union htu, htus, card_range], by simp⟩,
end

lemma eisenstein {f : polynomial R} {P : ideal R} (hP : P.is_prime)
  (hfl : f.leading_coeff ∉ P)
  (hfP : ∀ n : ℕ, ↑n < degree f → f.coeff n ∈ P)
  (hfd0 : 0 < degree f) (h0 : f.coeff 0 ∉ P^2)
  (hu : ∀ x : R, C x ∣ f → is_unit x) : irreducible f :=
have hf0 : f ≠ 0, from λ _, by simp * at *,
have hf : f.map (mk_hom P) =
    C (mk_hom P (leading_coeff f)) * X ^ nat_degree f,
  from polynomial.ext (λ n, begin
    rcases lt_trichotomy ↑n (degree f) with h | h | h,
    { erw [coeff_map, ← mk_eq_mk_hom, eq_zero_iff_mem.2 (hfP n h),
        coeff_C_mul, coeff_X_pow, if_neg, mul_zero],
      rintro rfl, exact not_lt_of_ge degree_le_nat_degree h },
    { have : nat_degree f = n, from nat_degree_eq_of_degree_eq_some h.symm,
      rw [coeff_C_mul, coeff_X_pow, if_pos this.symm, mul_one, leading_coeff, this, coeff_map] },
    { rw [coeff_eq_zero_of_degree_lt, coeff_eq_zero_of_degree_lt],
      { refine lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) _,
        rwa ← degree_eq_nat_degree hf0 },
      { exact lt_of_le_of_lt (degree_map_le _) h } }
  end),
have hfd0 : 0 < f.nat_degree, from with_bot.coe_lt_coe.1
  (lt_of_lt_of_le hfd0 degree_le_nat_degree),
⟨mt degree_eq_zero_of_is_unit (�� h, by simp [*, lt_irrefl] at *),
begin
  rintros p q rfl,
  rw [map_mul] at hf,
  have : map (mk_hom P) p ∣ C (mk_hom P (p * q).leading_coeff) * X ^ (p * q).nat_degree,
    from ⟨map (mk_hom P) q, hf.symm⟩,
  rcases mul_eq_mul_prime_pow (show prime (X : polynomial (ideal.quotient P)),
    from prime_of_degree_eq_one_of_monic degree_X monic_X) hf with
      ⟨m, n, b, c, hmnd, hbc, hp, hq⟩,
  have hmn : 0 < m → 0 < n → false,
  { assume hm0 hn0,
    have hp0 : p.eval 0 ∈ P,
    { rw [← coeff_zero_eq_eval_zero, ← eq_zero_iff_mem, mk_eq_mk_hom, ← coeff_map],
      simp [hp, coeff_zero_eq_eval_zero, zero_pow hm0] },
    have hq0 : q.eval 0 ∈ P,
    { rw [← coeff_zero_eq_eval_zero, ← eq_zero_iff_mem, mk_eq_mk_hom, ← coeff_map],
      simp [hq, coeff_zero_eq_eval_zero, zero_pow hn0] },
    apply h0,
    rw [coeff_zero_eq_eval_zero, eval_mul, pow_two],
    exact ideal.mul_mem_mul hp0 hq0 },
  have hpql0 : (mk_hom P) (p * q).leading_coeff ≠ 0,
  { rwa [← mk_eq_mk_hom, ne.def, eq_zero_iff_mem] },
  have hp0 : p ≠ 0, from λ h, by simp * at *,
  have hq0 : q ≠ 0, from λ h, by simp * at *,
  have hmn0 : m = 0 ∨ n = 0,
  { rwa [nat.pos_iff_ne_zero, nat.pos_iff_ne_zero, imp_false, not_not,
      ← or_iff_not_imp_left] at hmn },
  have hbc0 : degree b = 0 ∧ degree c = 0,
  { apply_fun degree at hbc,
    rwa [degree_C hpql0, degree_mul_eq, nat.with_bot.add_eq_zero_iff] at hbc },
  have hmp : m ≤ nat_degree p,
    from with_bot.coe_le_coe.1
      (calc ↑m = degree (p.map (mk_hom P)) : by simp [hp, hbc0.1]
         ... ≤ degree p : degree_map_le _
         ... ≤ nat_degree p : degree_le_nat_degree),
  have hmp : n ≤ nat_degree q,
    from with_bot.coe_le_coe.1
      (calc ↑n = degree (q.map (mk_hom P)) : by simp [hq, hbc0.2]
         ... ≤ degree q : degree_map_le _
         ... ≤ nat_degree q : degree_le_nat_degree),
  have hpmqn : p.nat_degree = m ∧ q.nat_degree = n,
  { rw [nat_degree_mul_eq hp0 hq0] at hmnd, omega },
  rcases hmn0 with rfl | rfl,
  { left,
    rw [eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.1),
      is_unit_C],
    refine hu _ _,
    rw [← eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.1)],
    exact dvd_mul_right _ _ },
  { right,
    rw [eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.2),
      is_unit_C],
    refine hu _ _,
    rw [← eq_C_of_degree_le_zero (nat_degree_eq_zero_iff_degree_le_zero.1 hpmqn.2)],
    exact dvd_mul_left _ _ }
end⟩

#print axioms eisenstein

example (a b c d e : ℤ) (hab : a ^ 2 = b ^ 2 + 1) : a ^3 =


def X : ℕ × ℕ → ℕ :=
λ ⟨a, b⟩, let ⟨x, y⟩ := (3,4) in
begin
  exact _x.1
end

#eval 274 % 6
#eval 4 * 3 * 5 * 7 * 2 * 3

set_option class.instance_max_depth 10000

instance : fact (0 < 27720) := by norm_num

#eval 1624 % 420

example : ∀ x : zmod 2520,
  x^7 + 21* x^6 + 175 * x^5 + 735 * x^4 + 1624 * x^3 + 1764 * x^2 + 720 x
dec_trivial

#eval X (5,4)

#exit
import data.polynomial
#print subtyp
example : 1= 1 := rfl
#print subtype.forall
variables {R : Type*} [comm_ring R]
open polynomial

open_locale classical

example {f : polynomial R} (n : ℕ)
  (h : ∀ m, n ≤ m → polynomial.coeff f m = 0) :
  degree f < n :=
if hf0 : f = 0 then by simp [hf0, with_bot.bot_lt_coe]
else lt_of_not_ge (λ hfn, mt leading_coeff_eq_zero.1 hf0 (h (nat_degree f)
  (with_bot.coe_le_coe.1 (by simpa only [ge, degree_eq_nat_degree hf0] using hfn)))

#exit
import group_theory.quotient_group data.fintype.basic set_theory.cardinal

universe u

open_locale classical

theorem normal_of_index_2 {G : Type u} [group G] (S : set G) [is_subgroup S]
  (HS1 : ∃ g ∉ S, ∀ x, x ∈ S ∨ g * x ∈ S)
  (HS2 : bool ≃ quotient_group.quotient S)
  [fintype (quotient_group.quotient S)] (HS3 : fintype.card (quotient_group.quotient S) = 2)
  (HS4 : cardinal.mk (quotient_group.quotient S) = 2) : normal_subgroup S :=
let ⟨x, hxS, hx⟩ := HS1 in
have ∀ g h, g * h ∈ S → g ∈ S → h ∈ S,
  from λ g h ghS gS, (hx h).resolve_right
    (λ xhS, hxS $
      suffices (x * h) * (g * h)⁻¹ * g ∈ S, by simpa [mul_assoc, mul_inv_rev],
      is_submonoid.mul_mem
        (is_submonoid.mul_mem xhS (is_subgroup.inv_mem ghS)) gS),
have ∀ g h, (g ∈ S ↔ h ∈ S) → g * h ∈ S,
  from λ g h ghS, (hx g).elim
    (λ gS, is_submonoid.mul_mem gS (ghS.1 gS))
    (λ xgS, (hx h).elim sorry
      (λ xhS, (is_subgroup.mul_mem_cancel_left S ((hx x).resolve_left hxS)).1
        _)),
{ normal :=

λ n hnS g, (hx g).elim sorry
  (λ h, begin



  end)

λ n hnS g, (hx g).elim
    (λ hgS, is_submonoid.mul_mem (is_submonoid.mul_mem hgS hnS) (is_subgroup.inv_mem hgS))
    begin
      assume hxgS,
      have hgS : g ∉ S, from sorry,


    end


}




#exit
import linear_algebra.basic tactic

universes u v

open linear_map

variables {R : Type u} [ring R] {M : Type v} [add_comm_group M] [module R M]


lemma equiv_ker_prod_range (p : M →ₗ[R] M) (hp : p.comp p = p) : M ≃ₗ[R] ker p × range p :=
have h : ∀ m, p (p m) = p m := linear_map.ext_iff.1 hp,
{ to_fun := λ m, (⟨m - p m, mem_ker.2 $ by simp [h]⟩, ⟨p m, mem_range.2 ⟨m, rfl⟩⟩),
  inv_fun := λ x, x.1 + x.2,
  left_inv := λ m, by simp,
  right_inv := by { rintros ⟨⟨x, hx⟩, ⟨_, y, hy, rfl⟩⟩, simp [h, mem_ker.1 hx] },
  add := λ _ _, by simp [subtype.coe_ext, add_comm, add_left_comm, add_assoc, sub_eq_add_neg],
  smul := λ _ _, by simp [subtype.coe_ext, smul_sub] }

#exit
import tactic
set_option profiler true
example : 0 < 1 := by norm_num

example : 0 < 1 := zero_lt_one

#exit
import data.nat.prime data.nat.parity data.real.pi

example (x : ℕ) (h : (λ y : ℕ, 0 < y) x) : 0 < x := h

open nat --real

example : real.pi < 47 := by pi_upper_bound [1.9]


theorem goldbach_disproof : ¬ goldbach :=
begin
  assume h,
  rcases h 0 (by norm_num) with ⟨p, q, hp, hq, h⟩,
  simp at h,
  exact absurd hp (h.1.symm ▸ by norm_num)
end

variables {R : Type*} [comm_ring R]

lemma pow_dvd_pow_of_dvd {a b : R} (h : a ∣ b) (n : ℕ) : a ^ n ∣ b ^ n :=
let ⟨d, hd⟩ := h in ⟨d ^ n, hd.symm ▸ mul_pow _ _ _⟩

@[simp] lemma nat.cast_dvd {a b : ℕ} : a ∣ b → (a : R) ∣ (b : R) :=
λ ⟨n, hn⟩, ⟨n, by simp [hn]⟩

lemma dvd_sub_add_pow (p : ℕ) [hp : fact p.prime] (a b : R) :
  (p : R) ∣ (a + b)^p - (a ^ p + b ^ p) :=
begin
  rw [add_pow],
  conv in (finset.range (p + 1)) { rw ← nat.sub_add_cancel hp.pos },
  rw [finset.sum_range_succ, finset.sum_range_succ',
    nat.sub_add_cancel hp.pos],
  suffices : ↑p ∣ (finset.range (p - 1)).sum (λ i, a ^ (i + 1) * b ^
      (p - (i + 1)) * nat.choose p (i + 1)),
  { simpa },
  refine finset.dvd_sum _,
  intros,
  refine dvd_mul_of_dvd_right (nat.cast_dvd
    (nat.prime.dvd_choose (nat.succ_pos _) (by simp at *; omega) hp)) _
end

lemma dvd_add_pow_iff (p : ℕ) [fact p.prime] (a b : R) :
  (p : R) ∣ (a + b)^p ↔ (p : R) ∣ (a ^ p + b ^ p) :=
(dvd_add_iff_left ((dvd_neg _ _).2 (dvd_sub_add_pow p a b))).trans (by simp)

lemma dvd_sub_pow_of_dvd_sub
   : ∀  (k : ℕ) (p : ℕ) (a b : R) (c d : ℕ)
    (h : (p : R) ∣ c * a - d * b),
  (p^(k+1) : R) ∣ c * a^(p^k) - d * b^(p^k)
| 0     p a b c d := by simp
| (k+1) p a b c d := λ h, begin
  have :=
    (dvd_sub_pow_of_dvd_sub k p a b c d h),
  simp at this,
  rw [dvd_add_pow_iff] at this,
  have := dvd_sub_pow_of_dvd_sub _ _ _ _ this,
  simp at this,


end


lemma dvd_sub_pow_of_dvd_sub (R : Type*) [comm_ring R]
   : ∀  (k : ℕ) (p : ℕ) (a b : R) (h : (p : R) ∣ a - b),
  (p^(k+1) : R) ∣ a^(p^k) - b^(p^k)
| 0 := by simp
| (k+1) := λ p a b h, begin
  have := dvd_sub_pow_of_dvd_sub k p a b h,
  rw [← nat.cast_pow] at this,
  have := dvd_sub_pow_of_dvd_sub _ _ _ _ this,
  simp at this,


end



import data.analysis.topology tactic
example {α : Type*} [ring α] {f₁ f₂ g₁ g₂ df₁ df₂ dg₁ dg₂ Pf Pg: α}
  (hf : f₁ - f₂ = df₁* Pf + Pf * df₂)
  (hg : g₁ - g₂ = dg₁* Pg + Pg * dg₂) :
  g₁ * f₁ - g₂ * f₂ = 0 :=
begin
  rw [sub_eq_iff_eq_add] at hf hg,
  substs f₁ g₁,
  simp only [mul_add, add_mul, mul_assoc, neg_mul_eq_mul_neg, ← mul_neg_eq_neg_mul_symm],
  simp only [add_left_comm, sub_eq_add_neg, add_assoc],
  abel,


end


#exit
import data.nat.prime tactic

lemma ahj (x : ℤ): (x + 1)^2 = x^2 + 2 * x + 1  :=
by ring
#print ahj
theorem subrel_acc {α : Type*} {r s : α → α → Prop} {x : α}
  (hrs : ∀ x y, s x y → r x y) (h : acc r x) : acc s x :=
acc.rec_on h (λ x hx ih, acc.intro x (λ y hsyx, ih y (hrs y x hsyx)))

theorem acc_of_lt {α : Type*} {r : α → α → Prop} {x y : α} (hr : r y x)
  (h : acc r x) : acc r y :=
by cases h; tauto

#print nat.factors

import algebra.associated

def SUBMISSION := Π {R : Type*} [comm_ring R] {u r : R} {n : ℕ},
  by exactI Π (hr : r ^ n = 0) (hu : is_unit u), is_unit (u + r)

notation `SUBMISSION` := SUBMISSION

theorem unit_add_nilpotent {R : Type*} [comm_ring R] {u r : R} {n : ℕ} (hr : r ^ n = 0)
  (hu : is_unit u) : is_unit (u + r) := sorry

theorem submission : SUBMISSION := @unit_add_nilpotent
#print axioms unit_add_nilpotent


#exit
import data.polynomial

variables {R : Type*} {S : Type*}

open function polynomial

example [integral_domain R] [integral_domain S] (i : R →+* S) (hf : injective i)
  {f : polynomial R} (hf0 : 0 < degree f) (hfm : f.monic) :
  (irreducible (f.map i) ∧ ∀ x : R, C x ∣ f → is_unit (C x)) ↔
    irreducible f  :=
begin
  split,
  { rintros ⟨hifm, hfC⟩,
    split,
    { exact mt degree_eq_zero_of_is_unit (λ h, absurd hf0 (h ▸ lt_irrefl _)) },
    { rintros g h rfl,
      cases hifm.2 (g.map i) (h.map i) (map_mul _) with hug huh,
      { have := degree_eq_zero_of_is_unit hug,
        rw [degree_map_eq_of_injective hf] at this,
        rw [eq_C_of_degree_eq_zero this],
        refine or.inl (hfC _ _),
        rw ← eq_C_of_degree_eq_zero this,
        exact dvd_mul_right _ _ },
      { have := degree_eq_zero_of_is_unit huh,
        rw [degree_map_eq_of_injective hf] at this,
        rw [eq_C_of_degree_eq_zero this],
        refine or.inr (hfC _ _),
        rw ← eq_C_of_degree_eq_zero this,
        exact dvd_mul_left _ _ } } },
  { assume hif,
    split,
    { split,
      { refine mt degree_eq_zero_of_is_unit (λ h, _),
        rw [degree_map_eq_of_injective hf] at h,
        exact absurd hf0 (h ▸ lt_irrefl _) },
      { rintros g h hm,
         } } }



end

#exit
import algebra.big_operators field_theory.finite field_theory.finite_card

variables {G R : Type} [group G] [integral_domain R] [fintype G] [decidable_eq G] [decidable_eq R]

open_locale big_operators add_monoid

open finset

def to_hom_units {G M : Type*} [group G] [monoid M] (f : G →* M) : G →* units M :=
{ to_fun := λ g,
    ⟨f g, f (g⁻¹),
      by rw [← monoid_hom.map_mul, mul_inv_self, monoid_hom.map_one],
      by rw [← monoid_hom.map_mul, inv_mul_self, monoid_hom.map_one]⟩,
  map_one' := units.ext (monoid_hom.map_one _),
  map_mul' := λ _ _, units.ext (monoid_hom.map_mul _ _ _) }

@[simp] lemma coe_to_hom_units {G M : Type*} [group G] [monoid M] (f : G →* M) (g : G):
  (to_hom_units f g : M) = f g := rfl

def preimage_equiv {H : Type} [group H] (f : G →* H) (x y : H) :
  f ⁻¹' {x} ≃ f ⁻¹' {y} := sorry

lemma sum_subtype {α M : Type*} [add_comm_monoid M]
  {p : α → Prop} {F : fintype (subtype p)} {s : finset α} (h : ∀ x, x ∈ s ↔ p x) {f : α → M} :
  ∑ a in s, f a = ∑ a : subtype p, f a :=
have (∈ s) = p, from set.ext h,
begin
  rw ← sum_attach,
  resetI,
  subst p,
  congr,
  simp [finset.ext]
end

variable (G)
lemma is_cyclic.exists_monoid_generator [is_cyclic G] :
  ∃ x : G, ∀ y : G, y ∈ powers x := sorry

open_locale classical

lemma sum_units_subgroup (f : G →* R) (hf : f ≠ 1) : ∑ g : G, f g = 0 :=
let ⟨x, hx⟩ := is_cyclic.exists_monoid_generator (set.range (to_hom_units f)) in
-- have hx1 : x ≠ 1, from sorry,
calc ∑ g : G, f g
    = ∑ g : G, to_hom_units f g : rfl
... = ∑ b : units R in univ.image (to_hom_units f),
      (univ.filter (λ a, to_hom_units f a = b)).card • b :
        sum_comp (coe : units R → R) (to_hom_units f)
... = ∑ b : units R in univ.image (to_hom_units f),
      fintype.card (to_hom_units f ⁻¹' {b}) • b :
  sum_congr rfl (λ b hb, congr_arg2 _ (fintype.card_of_finset' _ (by simp)).symm rfl)
... = ∑ b : units R in univ.image (to_hom_units f),
      fintype.card (to_hom_units f ⁻¹' {x}) • b :
  sum_congr rfl (λ b hb, congr_arg2 _ (fintype.card_congr (preimage_equiv _ _ _)) rfl)
... = ∑ b : set.range (to_hom_units f),
      fintype.card (to_hom_units f ⁻¹' {x}) • ↑b : sum_subtype (by simp)
... = fintype.card (to_hom_units f ⁻¹' {x}) * ∑ b : set.range (to_hom_units f), (b : R) :
  by simp [mul_sum, add_monoid.smul_eq_mul]
... = (fintype.card (to_hom_units f ⁻¹' {x}) : R) * 0 : (congr_arg2 _ rfl $
  calc ∑ b : set.range (to_hom_units f), (b : R)
      = ∑ n in range (order_of x), x ^ n :
    eq.symm $ sum_bij (λ n _, x ^ n) (by simp) (by simp)
      (λ m n hm hn, pow_injective_of_lt_order_of _ (by simpa using hm) (by simpa using hn))
      (λ b hb, let ⟨n, hn⟩ := hx b in ⟨n % order_of x, mem_range.2 (nat.mod_lt _ (order_of_pos _)),
        by rw [← pow_eq_mod_order_of, hn]⟩)
  ... = _ : begin  end)
... = 0 : mul_zero _


#print order_of_

import tactic
#print nat.prime

example : ∀ {p : ℕ} [fact p.prime] : ∀ m, m ∣ p → m = 1 ∨ m = p := by library_search
theorem a_pow_4_sub_b_pow_4 (a b : ℕ) : a ^ 4 - b ^ 4 = (a - b) * (a + b) * (a ^ 2 + b ^ 2) :=
if h : b ≤ a
then
  have b ^ 4 ≤ a ^ 4, from nat.pow_le_pow_of_le_left h _,
  int.coe_nat_inj $ by simp [int.coe_nat_sub h, int.coe_nat_sub this]; ring
else
  have a ^ 4 ≤ b ^ 4, from nat.pow_le_pow_of_le_left (le_of_not_ge h) _,
  by rw [nat.sub_eq_zero_of_le (le_of_not_ge h), nat.sub_eq_zero_of_le this]; simp

#exit
import group_theory.sylow

theorem order_of_eq_prime {G : Type*} [group G] [fintype G] [decidable_eq G] {g : G} {p : ℕ}
  (h : p.prime) (hg : g^p = 1) (hg1 : g ≠ 1) : order_of g = p :=
(h.2 _ (order_of_dvd_of_pow_eq_one hg)).resolve_left (mt order_of_eq_one_iff.1 hg1)

open_locale classical

theorem zagier (R : Type) [ring R]
  [fintype (units R)] : fintype.card (units R) ≠ 5 :=
λ h5 : fintype.card (units R) = 5,
let ⟨x, hx⟩ := sylow.exists_prime_order_of_dvd_card (show nat.prime 5, by norm_num)
  (show 5 ∣ fintype.card (units R), by rw h5) in
have hx5 : (x : R)^5 = 1,
  by rw [← units.coe_pow, ← hx, pow_order_of_eq_one, units.coe_one],
if h2 : (2 : R) = 0
then
have ((x : R)^3 + x^2 + 1) ^ 3 = 1,
  from calc ((x : R)^3 + x^2 + 1)^3
      = (x : R)^5 * (x^4 + 3 * x^3 + 3 * x^2 + 4 * x + 6) + 3 * x^4
          + 3 * x^3 + 3 * x^2 + 1 :
            by simp [mul_add, add_mul, pow_succ, add_comm, mul_assoc,
              add_assoc, add_left_comm, bit0, bit1]
  ... = 2 * (2 * x^4 + 3 * x^3 + 3 * x^2 + 2 * x + 3) + 1 :
            by rw hx5; simp [mul_add, add_mul, pow_succ, add_comm, mul_assoc,
              add_assoc, add_left_comm, bit0, bit1]
  ... = 1 : by rw [h2, zero_mul, zero_add],
let y : units R := units.mk
  ((x : R)^3 + x^2 + 1)
  (((x : R)^3 + x^2 + 1)^2)
  (eq.symm (this.symm.trans $ pow_succ _ _))
  (eq.symm (this.symm.trans $ pow_succ' _ _)) in
have hx1 : x ≠ 1,
from λ hx1, absurd hx (by simp [hx1]; norm_num),
have hx0 : (x : R)^2 * (x + 1) ≠ 0,
  from λ h, hx1 $ units.ext $ calc
    (x : R) = x - (x ^ (-2 : ℤ) : units R) * ((x ^ 2) * (x + 1)) :
      by rw [h, mul_zero, sub_zero]
    ... =  x - (x ^ (-2 : ℤ) * x ^ (2 : ℤ) : units R) * (x + 1) :
      by rw [units.coe_mul, mul_assoc]; refl
    ... = (x : R) - (x + 1) : by simp
    ... = 1 - 2 : by simp [mul_add, add_mul, pow_succ, add_comm, mul_assoc,
              add_assoc, add_left_comm, bit0, bit1]; abel
    ... = 1 : by rw [h2, sub_zero],
have hy1 : y ≠ 1, from mt (congr_arg (coe : units R → R)) $
  calc (y : R) = ((x : R)^3 + x^2 + 1) : rfl
  ... = (x^2 * (x + 1)) + 1 : by simp [mul_add, add_mul, pow_succ, add_comm, mul_assoc,
              add_assoc, add_left_comm, bit0, bit1]
  ... ≠ 0 + (1 : units R) : mt add_right_cancel hx0
  ... = 1 : by simp,
have hy3 : order_of y = 3, from order_of_eq_prime (by norm_num) (units.ext this) hy1,
absurd (show 3 ∣ 5, by rw [← h5, ← hy3]; exact order_of_dvd_card_univ) (by norm_num)
else
have hn1 : (-1 : R) ≠ 1,
  from λ h, h2 $
    calc (2 : R) = 1 + 1 : by norm_num
    ... = 1 + 1 : by norm_num
    ... = 1 + -1 : by rw h
    ... = 0 : by norm_num,
have hn1 : order_of (-1 : units R) = 2,
  from order_of_eq_prime (by norm_num)
    (units.ext $ by norm_num)
    (mt (congr_arg (coe : units R → R)) (by convert hn1)),
absurd (show 2 ∣ 5, by rw [← h5, ← hn1]; exact order_of_dvd_card_univ) (by norm_num)


#exit


import algebra.big_operators

variables {α : Type*} {β : Type*}

def list.coproduct (s : list α) (t : list β) : list (α ⊕ β) :=
s.map sum.inl ++ t.map sum.inr

lemma list.nodup_coproduct {s : list α} {t : list β} :
  (s.coproduct t).nodup ↔ s.nodup ∧ t.nodup :=
by simp [list.coproduct, list.nodup_append,
    list.nodup_map_iff (@sum.inl.inj _ _),
    list.nodup_map_iff (@sum.inr.inj _ _),
    list.disjoint]

lemma list.sum_coproduct {γ : Type*} [add_monoid γ] {s : list α} {t : list β} (f : α ⊕ β → γ) :
  ((s.coproduct t).map f).sum = (s.map (λ a, f (sum.inl a))).sum + (t.map (λ b, f (sum.inr b))).sum :=
by simp [list.coproduct]

def multiset.coproduct (s : multiset α) (t : multiset β) : multiset (α ⊕ β) :=
s.map sum.inl + t.map sum.inr

lemma multiset.nodup_coproduct {s : multiset α} {t : multiset β} :
  (s.coproduct t).nodup ↔ s.nodup ∧ t.nodup :=
quotient.induction_on₂ s t (λ _ _, list.nodup_coproduct)

lemma multiset.sum_coproduct {γ : Type*} [add_comm_monoid γ] {s : multiset α} {t : multiset β}
  (f : α ⊕ β → γ) :
  ((s.coproduct t).map f).sum =
    (s.map (λ a, f (sum.inl a))).sum + (t.map (λ b, f (sum.inr b))).sum :=
by simp [multiset.coproduct]

def finset.coproduct (s : finset α) (t : finset β) : finset (α ⊕ β) :=
⟨multiset.coproduct s.1 t.1, multiset.nodup_coproduct.2 ⟨s.2, t.2⟩⟩

open_locale big_operators

lemma finset.sum_coproduct {γ : Type*} [add_comm_monoid γ]
  {s : finset α} {t : finset β} (f : α ⊕ β → γ) :
  ∑ x in s.coproduct t, f x = ∑ a in s, f (sum.inl a) + ∑ b in t, f (sum.inr b) :=
multiset.sum_coproduct _



#exit
import data.quot data.setoid data.fintype.basic

instance decidable_is_empty' (α : Type*) [decidable_eq α] [fintype α]
  (S : set α) [decidable_pred S] : decidable (S = ∅) :=
decidable_of_iff (∀ x : α, x ∉ S) (by simp [set.ext_iff])

meta def quotient_choice {α β : Type} {s : setoid β}
  (f : α → quotient s) : quotient (@pi_setoid _ _ (λ a : α, s)) :=
quotient.mk (λ a : α, quot.unquot (f a))

example : false :=
let x : Π (quotient_choice : Π {α β : Type} [s : setoid β]
    (f : α → quotient s), quotient (@pi_setoid _ _ (λ a : α, s))),
  decidable false := λ quotient_choice,
-- ⊤ is the always true relation
by letI : setoid bool := ⊤; exact
quot.rec_on_subsingleton (@quotient_choice (@quotient bool ⊤) bool ⊤ id)
  (λ f, decidable_of_iff (f ⟦ff⟧ ≠ f ⟦tt⟧)
    (iff_false_intro (not_not_intro (congr_arg f (quotient.sound trivial))))) in
@of_as_true _ (x @quotient_choice) begin
  change x (@quotient_choice) with is_true _,

end



#exit

axiom callcc (α β : Prop) : ((α → β) → α) → α

example {p : Prop} : p ∨ ¬ p :=
callcc _ false (λ h, or.inr (h ∘ or.inl))

#exit
import tactic

#simp only [int.coe_nat_succ]

variables {α : Type*}

def le' (τ σ : α → α → Prop) := ∀ a b : α, τ a b → σ a b
notation τ ` ⊆ ` σ := le' τ σ

/- We now define the composition of two binary relations τ and σ
(denoted τ ∘ σ) as : for all a b, (τ ∘ σ) a b if and only if there
exists c, such that τ a c ∧ σ c b -/
def comp (τ σ : α → α → Prop) :=
  λ a b : α, ∃ c : α, τ a c ∧ σ c b
notation τ ∘ σ := comp τ σ

/- Prove that ⊆ is both reflexive and transitive -/
theorem le'_refl : @reflexive (α → α → Prop) le' :=
by dunfold reflexive; tauto

theorem le'_trans : @transitive (α → α → Prop) le' :=
by dunfold transitive; tauto

/- Prove that if two binary relations are reflexive, then so are their
compositions-/
theorem comp_refl {τ σ : α → α → Prop}
  (h₀ : reflexive τ) (h₁ : reflexive σ) :
  reflexive (τ ∘ σ) :=
by dunfold comp reflexive; tauto

/- Prove that composition is associative -/
theorem comp_assoc : @associative (α → α → Prop) comp :=
by simp [function.funext_iff, comp, associative]; tauto

/- Prove that a binary relation τ is transitive if and only if
(τ ∘ τ) ⊆ τ -/
theorem trans_iff_comp_le' {τ : α → α → Prop} :
  transitive τ ↔ (τ ∘ τ) ⊆ τ :=
⟨by dunfold transitive comp le'; tauto,
λ h x y z hxy hyz, h _ _ ⟨y, hxy, hyz⟩⟩

theorem sum_xx14n1 : ∀ n : ℕ,
  6 * (range (n + 1)).sum (λ n : ℕ, n * (2 * n - 1)) = n * (n + 1) * (4 * n - 1)
| 0     := rfl
| 1     := rfl
| (n+2) :=
have h1 : 0 < 4 * (n + 2),
  from mul_pos (by norm_num) (nat.succ_pos _),
have h2 : 0 < 2 * (n + 2),
  from mul_pos (by norm_num) (nat.succ_pos _),
have h3 : 0 < 4 * (n + 1),
  from mul_pos (by norm_num) (nat.succ_pos _),
begin
  rw [sum_range_succ, mul_add, sum_xx14n1],
  refine int.coe_nat_inj _,
  push_cast,
  rw [int.coe_nat_sub h1, int.coe_nat_sub h2, int.coe_nat_sub h3],
  push_cast,
  ring
end

#exit
import data.zmod.basic

example : 1 = 1 := rfl

#eval let n := 14 in ((finset.range n).filter $ λ r, 3 ∣ r ∨ 5 ∣ r).sum (λ n, n)

def solution' : fin 15 → ℕ
| ⟨0, _⟩ := 0
| ⟨1, _⟩ := 0
| ⟨2, _⟩ := 0
| ⟨3, _⟩ := 0
| ⟨4, _⟩ := 3
| ⟨5, _⟩ := 3
| ⟨6, _⟩ := 8
| ⟨7, _⟩ := 14
| ⟨8, _⟩ := 14
| ⟨9, _⟩ := 14
| ⟨10, _⟩ := 23
| ⟨11, _⟩ := 33
| ⟨12, _⟩ := 33
| ⟨13, _⟩ := 45
| ⟨14, _⟩ := 45
| ⟨n + 15, h⟩ := absurd h dec_trivial




theorem solution_valid (n : ℕ) : solution n =
  ((finset.range n).filter $ λ r, 3 ∣ r ∨ 5 ∣ r).sum (λ n, n) := rfl

#exit

#eval (∀ a b : zmod 74, a^2 - 37 * b^2 ≠ 3 : bool)

theorem no_solns : ¬ ∃ (a b : ℤ), a^2 - 37 * b^2 = 3 :=


lemma p11 : nat.prime 11 := by norm_num
lemma p71 : nat.prime 71 := by norm_num

open_locale classical

def totient' (n : ℕ) : ℕ := ((nat.factors n).map (λ n, n-1)).prod

def ptotient (n : ℕ+) : ℕ+ := ⟨totient' n, sorry⟩

def mult_5 (n : ℕ+) : ℕ := (multiplicity 5 n.1).get sorry

def compute_mod_p (p : ℕ+) :=
--if p = 101 then 0 else
let p₁  := p - 1 in
let m₁  := mult_5 p₁ in
let m₁5 := 5^m₁ in
let p₁m₁ : ℕ+ := ⟨p₁ / m₁5, sorry⟩ in
let p₂  := ptotient p₁m₁ in
let i := (5 : zmod p) ^
  ((5^(6 - 1 - m₁ : zmod p₂).1 : zmod p₁m₁).1 * m₁5) in
(i^4 + i^3 + i^2 + i + 1).1
 #eval let x := 5^5^3 in let a := x^4 + x^3 + x^2 + x + 1 in a
#eval 5^5^3
#eval (62500 : ℚ) / 5^6
#eval ptotient 1122853751
#eval mult_5 1122853750

#eval let x := 2^3^4 in let a := x^2 + x + 1 in
(multiplicity 3 (nat.min_fac a - 1)).get sorry



-- #eval nat.find (show ∃ n, let p : ℕ+ := ⟨10 * n + 1, nat.succ_pos _⟩ in nat.prime p ∧
--   compute_mod_p p = 0, from sorry)


meta def akkgnd : ℕ+ → tactic unit :=
λ n, if nat.prime n ∧ compute_mod_p n = 0
then tactic.trace "Answer is " >> tactic.trace n.1
else akkgnd (n - 10)




--#eval (list.range 500).filter (λ n, nat.prime n ∧ n % 5 = 1)
--#eval (list.range 1).map (λ n : ℕ, (compute_mod_p ⟨10 * n + 1, sorry⟩).map fin.val fin.val)
--#eval (nat.prime 1111 : bool)

lemma pow_eq_mod_card {α : Type*} [group α] [fintype α] (a : α) (n : ℕ) :
  a ^ n = a ^ (n % fintype.card α) :=
calc a ^ n = a ^ (n % order_of a) : pow_eq_mod_order_of
... = a ^ (n % fintype.card α % order_of a) :
  congr_arg2 _ rfl (nat.mod_mod_of_dvd _ order_of_dvd_card_univ).symm
... = a ^ (n % fintype.card α) : eq.symm pow_eq_mod_order_of
#eval (5 ^ 105 : zmod 131)
#eval (52 ^ 5 : zmod 131)
#eval (finset.range 200).filter (λ n : ℕ, n.prime ∧ n % 5 = 1 )
#eval nat.totient 26
-- #eval 5 ^ 26 % 31
-- #eval 25 ^ 5 % 31

lemma fivefiveeqone (n : ℕ) (hn : 0 < n): (5 ^ 5 ^ n : zmod 11) = -1 :=
have (5 : zmodp 11 p11) ^ 5 = 1, from rfl,
suffices units.mk0 (5 : zmodp 11 p11) dec_trivial ^ 5 ^ n = 1,
  by rw [units.ext_iff] at this; simpa,
have h1 : (5 ^ n : zmod 10) = 5,
  begin
    cases n with n,
    { simp [*, lt_irrefl] at * },
    clear hn,
    induction n,
    { refl },
    { rw [pow_succ, n_ih],
      refl }
  end,
have h2 : 5 ^ n % 10 = 5,
  from calc 5 ^ n % 10 = 5 % 10 :
    (zmod.eq_iff_modeq_nat' dec_trivial).1 (by simpa)
  ... = 5 : rfl,
have h3 : fintype.card (units (zmodp 11 p11)) = 10,
  by rw zmodp.card_units_zmodp; refl,
by rw [pow_eq_mod_card, h3, h2]; refl

@[simp] lemma coe_unit_of_coprime {n : ℕ+} (x : ℕ) (hxn : x.coprime n) :
  (zmod.unit_of_coprime x hxn : zmod n) = x := rfl


lemma pow_eq_pow_mod_totient {n : ℕ+} {x p : ℕ} (hxn : nat.coprime x n)
  (t : ℕ+) (ht : nat.totient n = t) : (x : zmod n) ^ p = x ^ (p : zmod t).1 :=
suffices zmod.unit_of_coprime x hxn ^ p =
    zmod.unit_of_coprime x hxn ^ (p : zmod ⟨nat.totient n, nat.totient_pos n.2⟩).1,
  begin
    cases t with t ht, simp at ht,subst t,
    rwa [units.ext_iff, units.coe_pow, coe_unit_of_coprime, units.coe_pow, coe_unit_of_coprime] at this,
  end,
begin
  rw [pow_eq_mod_card],
  refine congr_arg2 _ rfl _,
  rw [zmod.val_cast_nat, zmod.card_units_eq_totient],
  refl
end
#eval 5^70 % 71


lemma poly_div : ∀ x : ℕ, 1 < x → (x^5 - 1) / (x - 1) =
    x^4 + x^3 + x^2 + x + 1 :=
λ x hx, have 1 ≤ x ^ 5, from nat.pow_pos (by linarith) _,
nat.div_eq_of_eq_mul_left
  (nat.sub_pos_of_lt hx)
    (by { rw [nat.mul_sub_left_distrib, mul_one],
      symmetry,
      apply nat.sub_eq_of_eq_add,
      rw [← nat.add_sub_assoc this],
      symmetry,
      apply nat.sub_eq_of_eq_add,
      ring })

lemma fivefivefiveeq : ∃ n : ℕ, ((5^5^5^5^5-1)/(5^5^(5^5^5-1)-1)) =
  (5 ^ 5 ^ n)^4 + (5 ^ 5 ^ n)^3 + (5 ^ 5 ^ n)^2 + (5 ^ 5 ^ n) + 1 :=
have hpos : 1 < 5^5^(5^5^5-1),
  from calc 1 = 1 ^ 5^(5^5^5-1) : by simp
  ... < 5^5^(5^5^5-1) : nat.pow_left_strict_mono
    (nat.pow_pos (by norm_num) _) (by norm_num),
⟨(5^5^5-1), begin
  rw [← poly_div (5 ^ 5 ^(5^5^5-1)) hpos, ← nat.pow_mul,
    ← nat.pow_succ, ← nat.succ_sub, nat.succ_sub_one],
  exact nat.pow_pos (by norm_num) _
end⟩

theorem fivefives :
  ¬ nat.prime ((5^5^5^5^5-1)/(5^5^(5^5^5-1)-1)) :=
begin
  cases fivefivefiveeq with n hn,
  rw hn, clear hn,


end
#exit
import tactic
class incidence (point line : Type) (incident_with : point → line → Prop) :=
  (I₁ : ∀ P Q, P ≠ Q → ∃! l, incident_with P l ∧ incident_with Q l)
  (I₂ : ∀ l, ∃ P Q, P ≠ Q ∧ incident_with P l ∧ incident_with Q l)
  (I₃ : ∃ P Q R, P ≠ Q ∧ Q ≠ R ∧ P ≠ R ∧
    ∀ l, ¬(incident_with P l ∧ incident_with Q l ∧ incident_with R l))

theorem thm_3p6p8 (point line : Type) (incident_with : point → line → Prop)
  [incidence point line incident_with] (P Q : point) (hPQ : P ≠ Q) :
  ∃ R, ∀ l, ¬(incident_with P l ∧ incident_with Q l ∧ incident_with R l) :=
begin
  rcases @incidence.I₃ _ _ incident_with _ with ⟨A, B, C, hAB, hBC, hAC, h⟩,
  rcases @incidence.I₁ _ _ incident_with _ _ _ hPQ with ⟨l, hPQl, lunique⟩,
  have : ¬ incident_with A l ∨ ¬ incident_with B l ∨ ¬ incident_with C l,
  { finish using h l },
  rcases this with hA | hB | hC,
  { use A, finish },
  { use B, finish },
  { use C, finish }
end
#print thm_3p6p8
#exit
import category_theory.limits.shapes.pullbacks

open category_theory
open category_theory.limits

universes v u

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞
#print cancel_epi
#print walking_span

def pushout_of_epi {X Y : C} (f : X ⟶ Y) [epi f] :
  is_colimit (pushout_cocone.mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f) :=
pushout_cocone.is_colimit.mk _
  pushout_cocone.inl
  (by intro; erw [category.id_comp])
  (begin
    intro s,
    rw cocone.w s,
    rw ← cancel_epi f,
    obviously,

  end)
  (begin simp, end)


theorem epi_of_pushout {X Y : C} (f : X ⟶ Y)
  (is_colim : is_colimit (pushout_cocone.mk (𝟙 Y) (𝟙 Y) rfl : pushout_cocone f f)) : epi f := sorry

#exit
import group_theory.sylow

open finset mul_action

open_locale classical
#print equiv_of_unique_of_unique
theorem has_fixed_point {G : Type} [group G] [fintype G] (hG65 : fintype.card G = 65)
  {M : Type} [fintype M] (hM27 : fintype.card M = 27) [mul_action G M] :
  ∃ m : M, ∀ g : G, g • m = m :=
have horbit : ∀ m : M, fintype.card (orbit G m) ∣ 65,
  begin
    assume m,
    rw [fintype.card_congr (orbit_equiv_quotient_stabilizer G m), ← hG65],
    exact card_quotient_dvd_card _,
  end,
have hdvd65 : ∀ n, n ∣ 65 ↔ n ∈ ({1, 5, 13, 65} : finset ℕ) :=
  λ n, ⟨λ h, have n ≤ 65 := nat.le_of_dvd (by norm_num) h,
    by revert h; revert n; exact dec_trivial,
  by revert n; exact dec_trivial⟩,
begin
  letI := orbit_rel G M,
  have horbit_card : ∀ m : quotient (orbit_rel G M),
    fintype.card {x // ⟦x⟧ = m} ∣ 65,
  { assume m,
    refine quotient.induction_on m (λ m, _),
    convert horbit m,
    exact set.ext (λ _, quotient.eq) },
  have := fintype.card_congr
    (equiv.sigma_preimage_equiv (quotient.mk : M → quotient (orbit_rel G M))),
  rw [fintype.card_sigma] at this,



end,
-- begin
--   rcases @incidence.I₃ _ _ incident_with _ with ⟨A, B, C, hAB, hBC, hAC, hABC⟩,

--   have : P ≠ B ∧ P ≠ C ∨ P ≠ A ∧ P ≠ C ∨ P ≠ A ∧ P ≠ B, { finish },
--   wlog hP : P ≠ B ∧ P ≠ C := this using [B C, A C, A B],
--   {  }

-- end


end
