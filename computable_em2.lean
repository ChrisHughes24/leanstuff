import data.set.lattice order.order_iso data.quot
#print fintype
universes u v
Π (X Y : C), (f : X ⟶ Z) (g : Y ⟶ Z)
noncomputable theory

axiom choice2_aux {α : Sort u} : { choice : α → α // ∀ (a b : α), choice a = choice b }

def choice2 : Π {α : Sort u}, α → α := λ _, choice2_aux.1

lemma choice2_spec : ∀ {α : Sort u} (a b : α), choice2 a = choice2 b := λ _, choice2_aux.2

axiom univalence : ∀ {α β : Sort u}, α ≃ β → α = β

lemma trunc.out2 {α : Sort u} (a : trunc α) : α := trunc.lift_on a choice2 choice2_spec

variables {α : Type*} {β : Type*}

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

section diaconescu
variable p : Sort u
include p

private def U (x : Sort u) := trunc (psum (trunc x) p)
private def V (x : Sort u) := trunc (psum (x → false) p)

private lemma exU : trunc (Σ' x : Sort u, U p x) :=
  trunc.mk ⟨punit, trunc.mk (psum.inl (trunc.mk punit.star))⟩
private lemma exV : trunc (Σ' x : Sort u, V p x) :=
  trunc.mk ⟨pempty, trunc.mk (psum.inl (λ h, pempty.rec_on _ h))⟩

/- TODO(Leo): check why the code generator is not ignoring (some exU)
   when we mark u as def. -/
private def u : Sort u := psigma.fst (choice2 (trunc.out2 (exU p)))

private def v : Sort u := psigma.fst (choice2 (trunc.out2 (exV p)))

set_option type_context.unfold_lemmas true
private lemma u_def : U p (u p) := psigma.snd (choice2 (trunc.out2 (exU p)))
private lemma v_def : V p (v p) := psigma.snd (choice2 (trunc.out2 (exV p)))

private lemma not_uv_or_p : psum ((u p) ≠ (v p)) p :=
psum.cases_on (trunc.out2 (u_def p))
  (assume hut : trunc (u p),
    psum.cases_on (trunc.out2 (v_def p))
      (assume hvf : v p → false,
        psum.inl (λ h, hvf (eq.rec_on h (trunc.out2 hut))))
      psum.inr)
  psum.inr

private lemma p_implies_uv (hp : p) : u p = v p :=
have hpred : U p = V p, from
  funext (assume x : Sort u,
    univalence
      { to_fun := λ _, trunc.mk (psum.inr hp),
        inv_fun := λ _, trunc.mk (psum.inr hp),
        left_inv := λ x, show trunc.mk _ = _, from subsingleton.elim _ _,
        right_inv := λ x, show trunc.mk _ = _, from subsingleton.elim _ _ }),
show (choice2 (trunc.out2 (exU p))).fst = (choice2 (trunc.out2 (exV p))).fst,
  from @eq.drec_on _ (U p)
    (λ α (h : (U p) = α),
      (choice2 (trunc.out2 (exU p))).fst =
      (@choice2 (Σ' x : Sort u, α x) (trunc.out2
        (eq.rec_on (show V p = α, from hpred.symm.trans h) (exV p)))).fst)
    (V p) hpred (by congr)

#print axioms p_implies_uv

theorem em : psum p (p → false) :=
psum.rec_on (not_uv_or_p p)
  (assume hne : u p ≠ v p, psum.inr (λ hp, hne (p_implies_uv p hp)))
  psum.inl
