import data.fintype

open tactic environment declaration

#eval fintype.card (equiv.perm (fin 5))
meta def mk_equiv_psigma (n : name) : tactic (expr × ℕ) :=
do e ← get_env,
match is_structure_like e n with
| some (0, n) := return (`(empty), 0)
| some (1, n) := do d ← get_decl n, _
end
