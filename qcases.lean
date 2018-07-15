import tactic.ring algebra.ordered_field tactic.find data.complex.basic

open tactic tactic.interactive interactive.types interactive lean.parser

namespace tactic.interactive 

meta def qcases (p : parse texpr) (n : parse types.using_ident) : tactic unit :=
do e ← to_expr p,
revert_kdependencies e,
refine ``(quotient.induction_on %%e _),
intro n,
`[intros]



end tactic.interactive

example  (x : multiset ℕ) (h : x ≠ 0) : x = sorry :=
begin
  qcases x using x,

end


#print expr
#print expr
#print opt_param
#print pexpr
#print refl2