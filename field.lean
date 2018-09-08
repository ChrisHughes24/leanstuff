import data.fintype tactic.find data.set.finite ring_theory.subring data.nat.choose

open tactic expr lean interactive interactive.types
open set finset

inductive T : Type 145903 
| mk : Type → T

def sublists_of_length {α : Type*} : Π (l : list α) (n : ℕ), list (list α) 
| l      0     := [[]]
| []     (n+1) := []
| (a::l) (n+1) := (sublists_of_length l n).map (list.cons a) ++
  (sublists_of_length l (n + 1)) 

example : (⟨0, dec_trivial⟩ : fin 1

#eval (sublists_of_length [1,2,3,4,5] 6).length

#eval choose 5 3

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

meta def get_fintype (e : expr) : tactic (list expr) :=
e.fold (pure []) $ λ e _ l, do l' ← l,
  (do t ← infer_type e,
  match t with
  | (app n _) := if n.const_name = `fintype then return (e::l') else return l'
  | _ := return l'
  end) <|> return l'

-- meta def is_fintype (e : expr) : tactic (list expr) :=
-- match e with
-- | (app n _) := if n.const_name = `fintype then return [e] else return []
-- | _         := return []
-- end

-- meta def is_fintype_type (e : expr) : tactic (list expr) :=
-- infer_type e >>= is_fintype

meta def is_fintype (e : expr) : tactic bool :=
match e with
| (app n _) := if n.const_name = `fintype then return tt else return ff
| _         := return ff
end

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

#eval (`(Prop) : expr).to_raw_fmt.to_string
universe z
meta def thingy : expr → tactic unit
| `(@eq (%%u) (%%a) (%%b)) := begin 
    
    
  end -- do trace u.to_raw_fmt.to_string, trace _x, skip
| _ := failure

#print nat.to_digits
meta def generalize_fintype : expr → tactic expr
| `(@eq (%%u) (%%a) (%%b)) := match a with
  | (mvar x y f)          := do b ← is_fintype f,
    match b with
    | tt := return `
    | ff := failure
  | (local_const _ _ _ f) := is_fintype f
  | (app f g)             := do lf ← get_fintype' f, lg ← get_fintype' g, return (lf ++ lg)
  | _                     := return []
  end
| `((%%a) ↔ (%%b)) := sorry
| e := return e
#reduce tactic.skip
#reduce (return () : tactic unit)
example : false :=
let x : ℕ := 1 in
have hx : x = 1 := rfl,
begin
  replace x := x,

end

example (s t : set ℕ) [fintype s] [fintype t] [decidable_pred t] (h : fintype.card ↥(s ∩ t) = 77) :
  fintype.card ↥(s ∪ t) = 9  :=
begin
  thing,
  fold_test_target_type,

end