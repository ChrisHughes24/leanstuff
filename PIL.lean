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

meta def normalize_hyp (lemmas : simp_lemmas) (hyp : expr) : tactic unit :=
do try (simp_hyp lemmas [] hyp)

meta def normalize_hyps : tactic unit :=
do hyps ← local_context,
lemmas ← list.mmap mk_const [``iff_iff_implies_and_implies,
``implies_iff_not_or, ``not_and_iff, ``not_or_iff, ``not_not_iff,
``not_true_iff, ``not_false_iff],
lemmas2 ← simp_lemmas.append simp_lemmas.mk lemmas,
hyps.mmap' (normalize_hyp lemmas2)

meta def add_fact (prf : expr) : tactic unit :=
do nh ← get_unused_name `h none,
p ← infer_type prf,
assertv nh p prf,
return ()

meta def is_conj (e : expr) : tactic bool :=
do t ← infer_type e,
return (is_app_of t `and)

meta def add_conjuncts : expr → tactic unit | e :=
do e1 ← mk_app `and.left [e],
monad.cond (is_conj e1) (add_conjuncts e1) (add_fact e1),
e2 ← mk_app `and.right [e],
monad.cond (is_conj e2) (add_conjuncts e2) (add_fact e2)

meta def split_conjs_at (h : expr) : tactic unit :=
do monad.cond (is_conj h)
(add_conjuncts h >> clear h)
skip

meta def split_conjs : tactic unit :=
do l ← local_context,
l.mmap' split_conjs_at

meta def deny_conclusion : tactic unit :=
do refine ```(classical.by_contradiction _),
nh ← get_unused_name `h none,
intro nh,
return ()

meta def find_disj : tactic (option expr) :=
do l ← local_context,
(first $ l.map
(λ h, do t ← infer_type h,
cond (is_app_of t `or)
(return (option.some h)) failed)) <|>
return none

meta def prop_prover_aux : ℕ → tactic unit
| 0 := fail "prop prover max depth reached"
| (nat.succ n) :=
do split_conjs,
contradiction <|>
do (option.some h) ← find_disj |
fail "prop_prover failed: unprovable goal",
cases h,
prop_prover_aux n,
prop_prover_aux n

meta def prop_prover : tactic unit :=
do deny_conclusion,
normalize_hyps,
prop_prover_aux 30

section
variables a b c d : Prop
example (h1 : a ∧ b) (h2 : b ∧ ¬ c) : a ∨ c :=
by prop_prover
example (h1 : a ∧ b) (h2 : b ∧ ¬ c) : a ∧ ¬ c :=
by prop_prover
-- not valid
-- example (h1 : a ∧ b) (h2 : b ∧ ¬ c) : a ∧ c :=
-- by prop_prover
example : ((a → b) → a) → a :=
by prop_prover
example : (a → b) ∧ (b → c) → a → c :=
by prop_prover
example (α : Type) (x y z w : α) :
x = y ∧ (x = y → z = w) → z = w :=
by prop_prover
example : ¬ (a ↔ ¬ a) :=
by prop_prover
end