import algebra.group.basic data.buffer

universe u

@[derive decidable_eq, derive has_reflect] inductive group_term : Type
| of : ℕ → group_term
| one : group_term
| mul : group_term → group_term → group_term
| inv : group_term → group_term

namespace group_term

instance : has_one group_term := ⟨group_term.one⟩
instance : has_mul group_term := ⟨group_term.mul⟩
instance : has_inv group_term := ⟨group_term.inv⟩
instance : has_repr group_term :=
⟨λ t, group_term.rec_on t (λ n, "X" ++ repr n) "1"
   (λ _ _ s₁ s₂, "(" ++ s₁ ++ " * " ++ s₂ ++ ")")
   (λ _ s, "(" ++ s ++ ")⁻¹")⟩

local attribute [pattern] has_mul.mul has_inv.inv

def eval {G : Type*} [group G] (f : ℕ → G) : group_term → G
| (of i) := f i
| 1 := 1
| (a * b) := eval a * eval b
| (a⁻¹) := (eval a)⁻¹

/-- `rel a b` is inhabited when group terms are equal as elements of a group. -/
inductive rel : group_term → group_term → Type
| assoc : ∀ a b c : group_term, rel (a * b * c) (a * (b * c))
| mul_one : ∀ a : group_term, rel (a * 1) a
| one_mul : ∀ a : group_term, rel (1 * a) a
| mul_inv_self : ∀ a : group_term, rel (a * a⁻¹) 1
| inv_mul_self : ∀ a : group_term, rel (a⁻¹ * a) 1
| mul_inv_left_cancel : ∀ a b : group_term, rel (a⁻¹ * (a * b)) b
| mul_inv_right_cancel : ∀ a b : group_term, rel (a * (a⁻¹ * b)) b
| mul_inv_rev : ∀ a b, rel ((a * b)⁻¹) (b⁻¹ * a⁻¹)
| inv_inv : ∀ a, rel (a⁻¹⁻¹) a
| one_inv : rel (1⁻¹) 1
| mul : ∀ {a b c d : group_term}, rel a c → rel b d → rel (a * b) (c * d)
| refl : ∀ a : group_term, rel a a
| symm : ∀ {a b}, rel a b → rel b a
| trans : ∀ {a b c : group_term}, rel a b → rel b c → rel a c

lemma eval_eq_of_rel {G : Type*} [group G] (f : ℕ → G) (e₁ e₂ : group_term)
  (h : rel e₁ e₂) : e₁.eval f = e₂.eval f :=
by induction h; simp [eval, mul_assoc, *]

open expr

@[inline] meta def rel.reflect : Π {a b : group_term}, rel a b → expr
| _ _ (rel.assoc a b c) := (app (app (app (const ``rel.assoc [])
  (reflect a)) (reflect b)) (reflect c))
| _ _ (rel.mul_one a) := app (const ``rel.mul_one []) (reflect a)
| _ _ (rel.one_mul a) := app (const ``rel.one_mul []) (reflect a)
| _ _ (rel.mul_inv_self a) := app (const ``rel.mul_inv_self []) (reflect a)
| _ _ (rel.inv_mul_self a) := app (const ``rel.inv_mul_self []) (reflect a)
| _ _ (rel.mul_inv_left_cancel a b) :=
  app (app (const ``rel.mul_inv_left_cancel []) (reflect a)) (reflect b)
| _ _ (rel.mul_inv_right_cancel a b) :=
  app (app (const ``rel.mul_inv_right_cancel []) (reflect a)) (reflect b)
| _ _ (@rel.mul a b c d h₁ h₂) := app (app (app (app (app (app
  (const ``rel.mul [])
  (reflect a)) (reflect b)) (reflect c))
  (reflect d)) (rel.reflect h₁)) (rel.reflect h₂)
| _ _ (rel.mul_inv_rev a b) := app (app (const ``rel.mul_inv_rev []) (reflect a)) (reflect b)
| _ _ (rel.inv_inv a) := app (const ``rel.inv_inv []) (reflect a)
| _ _ (rel.one_inv) := const ``rel.one_inv []
| _ _ (rel.refl a) := app (const ``rel.refl []) (reflect a)
| _ _ (@rel.symm a b h) := app (app (app (const ``rel.symm []) (reflect a))
  (reflect b)) (rel.reflect h)
| _ _ (@rel.trans a b c hab hbc) := app (app (app (app (app
  (const ``rel.trans []) (reflect a))
  (reflect b)) (reflect c)) (rel.reflect hab)) (rel.reflect hbc)

-- meta def rel.reflect : Π {a b : group_term}, rel a b → expr
-- | _ _ (rel.assoc a b c) := `(rel.assoc %%(reflect a) %%(reflect b) %%(reflect c))
-- | _ _ (rel.mul_one a) := `(rel.mul_one %%(reflect a))
-- | _ _ (rel.one_mul a) := `(rel.one_mul %%(reflect a))
-- | _ _ (rel.mul_inv_self a) := `(rel.mul_inv_self %%(reflect a))
-- | _ _ (rel.inv_mul_self a) := `(rel.inv_mul_self %%(reflect a))
-- | _ _ (rel.mul_inv_left_cancel a b) := `(rel.mul_inv_left_cancel %%(reflect a) %%(reflect b))
-- | _ _ (rel.mul_inv_right_cancel a b) := `(rel.mul_inv_right_cancel %%(reflect a) %%(reflect b))
-- | _ _ (@rel.mul a b c d h₁ h₂) :=
--   `(@rel.mul %%(reflect a) %%(reflect b) %%(reflect c) %%(reflect d)
--      %%(rel.reflect h₁) %%(rel.reflect h₂))
-- | _ _ (rel.mul_inv_rev a b) := `(rel.mul_inv_rev %%(reflect a) %%(reflect b))
-- | _ _ (rel.inv_inv a) := `(rel.inv_inv a)
-- | _ _ (rel.one_inv) := `(rel.one_inv)
-- | _ _ (rel.refl a) := `(rel.refl a)
-- | _ _ (@rel.symm a b h) := `(@rel.symm %%(reflect a) %%(reflect b) %%(rel.reflect h))
-- | _ _ (@rel.trans a b c hab hbc) :=
--   `(@rel.trans %%(reflect a) %%(reflect b) %%(reflect c) %%(rel.reflect hab) %%(rel.reflect hbc))

attribute [trans] rel.trans

meta def snormalize : Π (x : group_term), Σ y : group_term, rel x y
| (a * b * c) := let ⟨y, h⟩ := snormalize (a * (b * c)) in
  ⟨y, rel.trans (rel.assoc _ _ _) h⟩
| (1⁻¹) := ⟨1, rel.one_inv⟩
| (a * 1) := let ⟨y, h⟩ := snormalize a in ⟨y, rel.trans (rel.mul_one _) h⟩
| (of i) := ⟨(of i), rel.refl _⟩
| (1 * a) := let ⟨y, h⟩ := snormalize a in ⟨y, rel.trans (rel.one_mul _) h⟩
| (of i * (of j)⁻¹) := if hij : i = j
  then ⟨1, eq.rec_on hij $ rel.mul_inv_self _⟩
  else ⟨of i * (of j)⁻¹, rel.refl _⟩
| ((of i)⁻¹ * of j) := if hij : i = j
  then ⟨1, eq.rec_on hij $ rel.inv_mul_self _⟩
  else ⟨(of i)⁻¹ * of j, rel.refl _⟩
| ((of i) * ((of j)⁻¹ * a)) :=
  if hij : i = j
  then let ⟨y, h⟩ := snormalize a in
    ⟨y, rel.trans (show rel ((of i) * ((of j)⁻¹ * a)) a,
      from eq.rec_on hij (rel.mul_inv_right_cancel (of i) a)) h⟩
  else let ⟨y, h⟩ := snormalize ((of j)⁻¹ * a) in
    ⟨(of i) * y, rel.mul (rel.refl _) h⟩
| ((of i)⁻¹ * ((of j) * a)) :=
  if hij : i = j
  then let ⟨y, h⟩ := snormalize a in
    ⟨y, rel.trans (show rel ((of i)⁻¹ * ((of j) * a)) a,
      from eq.rec_on hij (rel.mul_inv_left_cancel (of i) a)) h⟩
  else let ⟨y, h⟩ := snormalize ((of j) * a) in
    ⟨(of i)⁻¹ * y, rel.mul (rel.refl _) h⟩
| ((a * b)⁻¹) := let ⟨y, h⟩ := snormalize (b⁻¹ * a⁻¹) in
  ⟨y, rel.trans (rel.mul_inv_rev _ _) h⟩
| (a⁻¹⁻¹) := let ⟨y, h⟩ := snormalize a in
  ⟨y, rel.trans (rel.inv_inv _) h⟩
| (of i)⁻¹ := ⟨(of i)⁻¹, rel.refl _⟩
| 1 := ⟨1, rel.refl _⟩
| (a * b) := let ⟨x, hx⟩ := snormalize a in let ⟨y, hy⟩ := snormalize b in
  ⟨x * y, rel.mul hx hy⟩

meta def normalize : Π (x : group_term), Σ y : group_term, rel x y
| x := let sn := snormalize x in
if x = sn.1 then ⟨x, rel.refl x⟩
else let n := normalize sn.1 in
⟨n.1, sn.2.trans n.2⟩

open tactic

meta def prove_rel (x y : group_term) : option (rel x y) :=
let nx := normalize x, ny := normalize y in
if h : nx.1 = ny.1
then some (rel.trans nx.2 (eq.rec_on h.symm ny.2.symm))
else none

-- meta def prove_rel_aux : expr → tactic unit
-- | `(rel %%xe %%ye) :=
-- do x ← eval_expr group_term xe,
--    y ← eval_expr group_term ye,
--    match prove_rel' x y with
--    | none := failure
--    | some e := tactic.exact (rel.reflect e)
--    end
-- | _ := failure

-- meta def prove_rel : tactic unit :=
-- target >>= prove_rel_aux

@[derive [monad, alternative]]
meta def group_m (α : Type) : Type :=
reader_t (ref (buffer expr)) tactic α

meta def read : group_m (ref (buffer expr)) := reader_t.read

meta def add_atom (e : expr) : group_m ℕ :=
⟨λ l, do es ← read_ref l,
  es.iterate failed (λ n e' t, t <|> (is_def_eq e e' $> n.1)) <|>
    (es.size <$ write_ref l (es.push_back e))⟩

meta def to_group_term : expr → group_m group_term
| `(%%a * %%b) :=
  do a' ← to_group_term a,
     b' ← to_group_term b,
     return (a' * b')
| `((%%a)⁻¹) :=
  do a' ← to_group_term a, return (a'⁻¹)
| `(@has_one.one _ _) := return 1
| e := do l ← read, n ← add_atom e, return (of n)

meta def to_group_rel : expr → group_m (expr × group_term × group_term )
| `(@eq %%G %%a %%b) :=
  do a' ← to_group_term a,
     b' ← to_group_term b,
     return (G, a', b')
| _ := failure

/-- Given an `l : buffer expr` return an `expr` representing a list containing
  whose elements are the elements represented by the `expr`s in `l`  -/
meta def to_list_expr (α : expr) (l : buffer expr) : tactic expr :=
l.reverse.foldl (mk_mapp `list.nil [α])
  (λ a l, do l ← l, mk_mapp `list.cons [α, a, l])

lemma eval_eq_of_rel' (G : Type*) [group G] (l : list G) (t₁ t₂ : group_term)
  (h : rel t₁ t₂) : t₁.eval (λ i, (l.nth i).get_or_else 1) =
  t₂.eval (λ i, (l.nth i).get_or_else 1) :=
eval_eq_of_rel _ _ _ h

meta def suffices_rel : tactic unit :=
using_new_ref mk_buffer $ λ l : ref (buffer expr),
  do t ← target,
  (G, t₁, t₂) ← reader_t.run (to_group_rel t) l,
  l ← read_ref l,
  l ← to_list_expr G l,
  p' ← tactic.mk_mapp `group_term.eval_eq_of_rel'
        [G, none, l, reflect t₁, reflect t₂],
  apply p', skip

meta def group_tac : tactic unit :=
using_new_ref mk_buffer $ λ l : ref (buffer expr),
  do t ← target,
  (G, t₁, t₂) ← reader_t.run (to_group_rel t) l,
  l ← read_ref l,
  l ← to_list_expr G l,
  match prove_rel t₁ t₂ with
  | none := do trace "t₁ = ",
      trace (repr t₁),
      trace "t₂ = ",
      trace (repr t₂), fail "terms aren't equal"
  | some p :=
      do p' ← tactic.mk_mapp `group_term.eval_eq_of_rel'
          [G, none, l, reflect t₁, reflect t₂, rel.reflect p],
      tactic.exact p'
  end

set_option profiler true

example {G : Type*} [group G] (a b c d e f g h i : G) :
  (d * a * b * b⁻¹ * c * c * c⁻¹ * (c⁻¹ * a * f * g * g)⁻¹ *
  g * (g⁻¹ * a * a⁻¹)⁻¹ * 1 * 1⁻¹ * a⁻¹ * (1 * a)) =
  d * a * c * g⁻¹ * g⁻¹ * f⁻¹ * a⁻¹ * c * g * g  :=
begin
  group_tac,
end

example {G : Type } [group G] (a b c d e f g h i : G) :
  (a * a⁻¹) = 1 :=
begin
  group_tac,
end

end group_term
