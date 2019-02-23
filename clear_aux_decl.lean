import tactic.basic tactic

open tactic

#print tactic.local_context
#print expr.is_aux_decl
#print tactic.clear
#print tactic.interactive.clear


namespace tactic.interactive

meta def clear_aux_decl_aux : list expr → tactic unit
| []     := skip
| (e::l) := do cond e.is_aux_decl (tactic.clear e) skip, clear_aux_decl_aux l

meta def clear_aux_decl : tactic unit :=
local_context >>= clear_aux_decl_aux

end tactic.interactive

meta def h : tactic unit :=
do l ← local_context, trace (l.filter (λ e : expr, e.is_aux_decl)).length


example (x y : ℕ) (h₁ : ∃ n : ℕ, n * 1 = 2) (h₂ : 1 + 1 = 2 → x * 1 = y) : x = y :=
let ⟨n, hn⟩ := h₁ in
begin
  clear_aux_decl,
  finish
end
