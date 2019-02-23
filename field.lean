import data.fintype tactic.find data.set.finite ring_theory.subring data.nat.choose tactic.find

open tactic expr lean interactive interactive.types
open set finset


meta def fold_test : expr → tactic (list (nat × string)) :=
λ e, do let l := e.fold [] (λ e n l, (n, e.to_string) :: l),
trace l, return l

meta def fold_test_type : expr → tactic (list (nat × string)) :=
λ e, do l ← e.fold (pure [])
  (λ e n l, (do t ← infer_type e, l ← l, return ((n, t.to_string) :: l)) <|> l),
  trace l, return l

meta def fold_test_target : tactic unit :=
target >>= fold_test >> skip

meta def fold_test_target_type : tactic unit :=
target >>= fold_test_type >> skip

/-- gets the type of any fintype in an expr -/
meta def get_fintype (e : expr) : tactic (list expr) :=
e.fold (pure []) $ λ e _ l, do l' ← l,
  (do t ← infer_type e,
  match t with
  | `(fintype _) := return (e::l')
  | _ := return l'
  end) <|> return l'

-- meta def is_fintype (e : expr) : tactic (list expr) :=
-- match e with
-- | (app n _) := if n.const_name = `fintype then return [e] else return []
-- | _         := return []
-- end

-- meta def is_fintype_type (e : expr) : tactic (list expr) :=
-- infer_type e >>= is_fintype

/-- checks is an expression is has type `fintype _` -/
meta def is_fintype (e : expr) : tactic bool :=
match e with
| (app n _) := if n.const_name = `fintype then return tt else return ff
| _         := return ff
end

/-- returns the type of an expr if it has type `fintype _` -/
meta def is_fintype_type (e : expr) : tactic expr :=
do f ← infer_type e,
  b ← is_fintype f,
  match b with
  | tt := return f
  | ff := failure
  end

-- meta def get_fintype' : expr → tactic (list expr)
-- | e := do l ← is_fintype_type e, match l with
--   | [] := match e with
--     | (mvar _ _ f)          := is_fintype f
--     | (local_const _ _ _ f) := is_fintype f
--     | (app f g)             := do lf ← get_fintype' f, lg ← get_fintype' g, return (lf ++ lg)
--     | _                     := return []
--     end
--   | _ := return l
-- end

-- meta def thing : tactic unit :=
-- do t ← target,
-- l ← get_fintype' t,
-- match l with
-- | [] := return ()
-- | (a :: l) := _match l >> pose `f none a >> reset_instance_cache >> skip
-- end
-- #print expr
-- lemma fintype_congr (α : Type*) [fintype α] (P : Π [fintype α], Prop) (h : P) (x : fintype α) : @P x :=
-- by convert h


-- meta def generalize_fintype : expr → tactic (list expr)
-- | `(@eq (%%u) (%%a) (%%b)) := match a with
--   | (mvar x y f)           := mcond (is_fintype f) (return [f]) failure
--   | (local_const _ _ _ f)  := mcond (is_fintype f) (return [f]) failure
--   | (app f g)              := do lf ← get_fintype f, lg ← get_fintype g, return (lf ++ lg)
--   | _                      := return []
--   end
-- | `((%%a) ↔ (%%b)) := match a with
--   | (mvar x y f)           := mcond (is_fintype f) (return [f]) failure
--   | (local_const _ _ _ f)  := mcond (is_fintype f) (return [f]) failure
--   | (app f g)              := do lf ← get_fintype f, lg ← get_fintype g, return (lf ++ lg)
--   | _                      := return []
--   end
-- | e := return []

-- #print expr.

-- meta def generalize_forall_aux (t : expr) (e : expr) (f : expr → expr) :
--   expr × (expr → expr) :=
-- cond (expr.alpha_eqv t e)
--   _
--   (e, f)


-- meta def generalize_forall (t : expr) : expr → (expr → expr) → tactic expr
-- | (const n l) f :=

-- #reduce tactic.skip
-- #reduce (return () : tactic unit)
-- example : false :=
-- let x : ℕ := 1 in
-- have hx : x = 1 := rfl,
-- begin
--   replace x := x,

-- end
#print cond._main
#print id_rhs
#find (tactic _ → option _)

meta def get_fintype' (e : expr) : tactic (list (expr × expr)) :=
e.fold (return []) $ λ e _ l, do l' ← l,
  (do t ← infer_type e,
  match t with
  | `(fintype _) := cond (has_var e) (return ((e, t) :: l')) (return l')
  | _ := return l'
  end) <|> return l'

meta def get_fintype_aux (e : expr) (t : expr) (l : tactic (list (expr × expr))) :
  tactic (list (expr × expr)) :=
  match t with
  | `(fintype _) := do l ← l, cond (has_var e) (return ((e, t) :: l)) (return l)
  | _ := l
  end

#eval (```((2 : ℕ) + 2) : expr ff).to_raw_fmt.to_string

#print expr.pi
meta def get_fintype₂ : expr → tactic (list (expr × expr))
| (const n l)           := do t ← infer_type (const n l), get_fintype_aux (const n l) t (pure [])
| (local_const n m i t) := get_fintype_aux (local_const n m i t) t (pure [])
| (app f x)             := do l₁ ← get_fintype₂ f, l₂ ← get_fintype₂ x, return (l₁ ++ l₂)
| (lam n i v e)         := do l₁ ← get_fintype₂ v, l₂ ← get_fintype₂ e, return (l₁ ++ l₂)
| (pi n i v e)          := do l₁ ← get_fintype₂ v, l₂ ← get_fintype₂ e, return (l₁ ++ l₂)
| _ := return []

#print simplify

#print monad
#print expr.replace
#reduce tactic
#print <|>
#print interaction_monad.result
#print tactic
#eval expr.get_nat_value

#print expr
#print tactic.simplify
meta def

meta def replace_fintype : Π (e : expr) (l : list (expr × expr)), tactic expr


example (s t : set ℕ) [fintype s] [fintype t] [decidable_pred t] (h : fintype.card ↥(s ∩ t) = 77) :
  fintype.card ↥(s ∪ t) = 9  :=
begin
  -- thing,
  -- fold_test_target_type,

end