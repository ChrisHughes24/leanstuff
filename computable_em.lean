import data.quot tactic
open classical
noncomputable theory

variables (p : Type) {α : Type*} {β : Type*}

inductive eq' (a : α) : α → Type
| refl : eq' a
infix ` =' `:50 := eq'

def eq'.symm : ∀ {a b : α}, a =' b → b =' a
| _ _ (eq'.refl _) := (eq'.refl _)

def eq'.trans : ∀ {a b c : α}, a =' b → b =' c → a =' c
| _ _ _ (eq'.refl _) (eq'.refl _) := (eq'.refl _)

def eq'.congr_arg (f : α → β): ∀ {a b : α}, a =' b → f a =' f b
| _ _ (eq'.refl a) := eq'.refl _

def eq'.cast : ∀ {a b : Type}, a =' b → a → b
| _ _ (eq'.refl a) := id

def U (x : Type) : Type := trunc (trunc x =' trunc unit ⊕ p)
def V (x : Type) : Type := trunc (trunc x =' trunc empty ⊕ p)

def exU : trunc (Σ x : Type, U p x) := trunc.mk ⟨unit, trunc.mk $ sum.inl (eq'.refl _)⟩
def exV : trunc (Σ x : Type, V p x) := trunc.mk ⟨empty, trunc.mk $ sum.inl (eq'.refl _)⟩

axiom choice' {α  : Type*} {β : α → Type*} {r : Π x, β x → Type*}
  (f : Π i, trunc (Σ b : β i, r i b)) :
  trunc (Π i, Σ b : β i, r i b)

lemma choice'2 {α  : Type*} {β : α → Type*} (f : Π a, trunc (β a)) :
  trunc (Π a, β a) :=
let g : Π a, trunc (Σ b : β a, unit) := λ a, trunc.map (λ x, ⟨x, ()⟩) (f a) in
trunc.map (by intros g a; exact (g a).1) (choice' g)

lemma choice3 {α : Type*} : trunc (Σ f : α → α, Π a b : α, f a =' f b) :=
trunc.rec_on_subsingleton (choice'2 (@trunc.mk α))
begin


end

def not_uv_or_p : ∀ (u : Σ x : Type, U p x) (v : Σ x : Type, V p x),
  trunc ((trunc u.fst =' trunc v.fst → empty) ⊕ p) :=
begin
  rintros ⟨u, hu⟩ ⟨v, hv⟩,
  dsimp [U, V] at *,
  refine trunc.lift_on hu (λ hu, _) (λ _ _, subsingleton.elim _ _),
  refine trunc.lift_on hv (λ hv, _) (λ _ _, subsingleton.elim _ _),
  cases hu with hu hu,
  { cases hv with hv hv,
    { refine trunc.mk (sum.inl (λ e, _)),
      have : trunc unit =' trunc empty, from eq'.rec_on hu (eq'.rec_on hv e),
      have : trunc empty, from this.cast (trunc.mk ()),
      refine trunc.lift_on this id (assume a, by cases a) },
    { exact trunc.mk (sum.inr hv) } },
  { exact trunc.mk (sum.inr hu) }
end

axiom funext' {β : α → Type*}
  {f₁ f₂ : Π x : α, β x} (h : ∀ x, f₁ x =' f₂ x) : f₁ =' f₂

axiom univalence {α β : Sort*} : α ≃ β → α =' β

noncomputable lemma trunc_eq'_trunc_of_true {α β : Sort*} : α → β → trunc α =' trunc β :=
λ a b, univalence ⟨λ _, trunc.mk b, λ _, trunc.mk a, λ _, subsingleton.elim _ _,
  λ _, subsingleton.elim _ _⟩

-- noncomputable def p_implies_uv (hp : p) (u : Σ x : Type, U p x)
--   (v : Σ x : Type, V p x) : u.fst =' v.fst :=
-- begin
--   have : U p =' V p,
--   { refine funext' (λ x, _),
--     exact trunc_eq'_trunc_of_true (sum.inr hp) (sum.inr hp), },
--   revert u v,
--   refine eq'.rec_on this _,
--   assume u v,
--   exact trunc_eq'_trunc_of_true _ _,
-- end

noncomputable def em : trunc (p ⊕ (p → empty)) :=
let fU : trunc (Π {α : Type → Type → Type}, (Π p : Type, Σ x : Type, α p x)) :=
  choice'2 (λ α, choice' (λ p, _))  in
let fV : trunc (Π p : Type, Σ x : Type, V p x) := choice' exV in
trunc.rec_on_subsingleton fU (assume fU', trunc.rec_on_subsingleton fV (assume fV',
  let exU := fU' p, exV := fV' p in
  have p → trunc exU.1 =' trunc exV.1,
    from λ hp, have U p =' V p, from funext'
        (λ x, trunc_eq'_trunc_of_true (sum.inr hp) (sum.inr hp)),
      begin
        revert exU exV fU' fV',
        dsimp [fU, fV],
        refine eq'.rec_on this _,
        intros,
        exact trunc_eq'_trunc_of_true _ _,
      end,

  trunc.mk begin
    refine sum.rec_on (not_uv_or_p p(fU p) (fV p)) _ _,
    { assume h,
      exact sum.inr (assume hp : p, h (p_implies_uv p hp _ _)) },
    { exact sum.inl }
end))
