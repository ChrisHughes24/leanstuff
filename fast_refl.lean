import data.nat.basic tactic data.nat.parity
open nat expr tactic

universes u v

lemma let_congr {α : Type u} {β : Type v} (assignment₁ assignment₂ : α) (body : β)
  (h : assignment₁ = assignment₂) : let a := assignment₁ in body = let a := assignment₂ in body :=
h ▸ rfl

meta def reduce : expr → tactic (expr × expr)
| (elet n t v b) :=
  do (v', p) ← reduce v,
  T ← infer_type (elet n t v b),
  let eq' := `(@eq.{1} (%%T) (%%(elet n t (var 0) b)) (%%(elet n t v b))),
  --eq' ← tactic.mk_mapp `eq [T, elet n t v b, elet n t (var 0) b],
  let motive : expr := lam `x default t eq',
  let
  p' ← tactic.mk_mapp `eq.rec [t, v, motive, p, v'],
  return (elet n t v' b, p')
| `((1 : ℕ) + (1 : ℕ)) := return (`(2 : ℕ), `(eq.refl (2 : ℕ)))
| e := do eq' ← tactic.mk_app `eq.refl [e], return (e, eq')

set_option trace.app_builder true
#eval reduce `(let n := 1 + 1 in n)

meta def blah : tactic unit :=
do (e₁, e₂) ← reduce `(let n := 1 + 1 in n), tactic.exact e₂

example : let n := 1 + 1 in n = let n := 2 in n := by blah

#eval
