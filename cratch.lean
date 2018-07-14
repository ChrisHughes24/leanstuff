import logic.function
open function

def f : (thunk ℕ) → ℕ  := λ _, 0

def g : ℕ → ℕ := λ _, 0

#print thunk

#eval f ((99 : ℕ) ^ 99 ^ 99) 

#eval g (99 ^ 99 ^ 99 ^ 99 ^ 99)


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
