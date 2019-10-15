import hott.init hott.types.sigma hott.types.nat
set_option pp.notation false
#print hott.univalence

namespace hott

local infix ` = `:50 := hott.eq

@[hott] lemma X : bool = bool := eq.refl _

@[hott] def Y (a b : unit) : ∀ (x y : a = b), x = y :=
punit.rec_on a (λ x, @eq.rec_on _ _ (λ b h, ∀ y, eq h y) _ _ $ 
  λ y, @eq.rec_on unit () (λ a, punit.rec_on a (eq (eq.refl ()))) () y (eq.refl _))

#print nat.no_confusion

@[hott] lemma eq.symm {α : Sort*} {x y : α} (h : x = y) : y = x := eq.rec_on h rfl

@[hott] example (a b : ℕ) : ∀ (x y : a = b), x = y :=
begin
  assume x,
  hinduction x,
  assume y,
  hinduction a,
  exact @eq.rec_on ℕ 0 begin end _ _ _ _,

end


@[hott] def bool_not : equiv bool bool :=
equiv.mk bnot $ is_equiv.mk _ bnot 
  (λ b, bool.rec_on b rfl rfl) (λ b, bool.rec_on b rfl rfl) 
    (λ b, bool.rec_on b rfl rfl)

axiom choice : Π {α : Sort*}, trunc 0 α → α 

noncomputable example : empty := 
let b := choice (trunc.tr tt) in
let e : bool = bool := ua bool_not in
let b' : bool := eq.cast e b in 
have hb' : b' = choice (trunc.tr ff), from sorry,
have h : b' = bnot b, from cast_ua bool_not b,
have h' : b' = b, from @eq.rec_on _ 
  (choice (trunc.tr ff)) (λ c _, b' = c) _ 
    (@eq.rec_on _ (choice (trunc.tr tt)) (λ c _, c = b) _ 
      (@eq.rec_on _ (trunc.tr ff) (λ c _, choice c = choice (trunc.tr ff)) _ 
        sorry
        rfl) 
      rfl) 
    hb',


end hott
