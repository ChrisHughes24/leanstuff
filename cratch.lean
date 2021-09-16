import data.set.function
import data.fintype.basic
import data.finset.basic
import data.fin
import tactic


open finset function

@[derive fintype, derive decidable_eq]
structure cell := (r : fin 9) (c : fin 9)

def row (i : fin 9) : finset cell := filter (λ a, a.r = i) univ
def col (i : fin 9) : finset cell := filter (λ a, a.c = i) univ
def box (i : fin 9) : finset cell := filter (λ a, a.r / 3 = i / 3 ∧ a.c / 3 = i % 3) univ

lemma mem_row (a : cell) (i : fin 9) : a ∈ row i ↔ a.r = i := by simp [row]
lemma mem_col (a : cell) (i : fin 9) : a ∈ col i ↔ a.c = i := by simp [col]
lemma mem_box (a : cell) (i j : fin 3) :
  a ∈ box i ↔ a.r / 3 = i / 3 ∧ a.c / 3 = i % 3 := by simp [box]

def same_row (a : cell) (b : cell) := a.r = b.r
def same_col (a : cell) (b : cell) := a.c = b.c
def same_box (a : cell) (b : cell) := (a.r / 3) = (b.r / 3) ∧ (a.c / 3) = (b.c / 3)

def cell_row (a : cell) : finset cell := row (a.r)
def cell_col (a : cell) : finset cell := col (a.c)
def cell_box (a : cell) : finset cell := box (3*(a.r / 3) + a.c / 3)

@[derive fintype, derive decidable_eq] 
def sudoku := cell → fin 9

def row_axiom (s : sudoku) : Prop := ∀ a b : cell, same_row a b → s a = s b → a = b
def col_axiom (s : sudoku) : Prop := ∀ a b : cell, same_col a b → s a = s b → a = b
def box_axiom (s : sudoku) : Prop := ∀ a b : cell, same_box a b → s a = s b → a = b

def normal_sudoku_rules (s : sudoku) : Prop := row_axiom s ∧ col_axiom s ∧ box_axiom s

@[simp] lemma card_row : ∀ (i : fin 9), finset.card (row i) = 9 := dec_trivial
@[simp] lemma card_col : ∀ (i : fin 9), finset.card (col i) = 9 := dec_trivial
@[simp] lemma card_box : ∀ (i : fin 9), finset.card (box i) = 9 := dec_trivial

lemma row_injective (s : sudoku) (h_row : row_axiom s) (i : fin 9) :
  ∀ a b ∈ row i, s a = s b → a = b :=
begin
  intros a b ha hb h_eq,
  have h_srow : same_row a b,
  { rw mem_row at ha hb,
    rw ← hb at ha,
    exact ha
  },
  apply h_row _ _ h_srow h_eq
end

lemma row_surjective (s : sudoku) (h_row : row_axiom s) (i v : fin 9) :
  ∃ c ∈ (row i), v = s c :=
finset.surj_on_of_inj_on_of_card_le 
  (λ c (hc : c ∈ row i), s c)
  (λ _ _, finset.mem_univ _)
  (row_injective s h_row i)
  (by simp) _
  (mem_univ _)


#exit
import ring_theory.polynomial.homogeneous

variables {σ R : Type*} [comm_semiring R]

namespace mv_polynomial

lemma homogeneous_submodule_eq_span_monomial (i : ℕ) :
  homogeneous_submodule σ R i =
    submodule.span R ((λ d, monomial d 1) '' { d : σ →₀ ℕ | d.sum (λ _, id) = i }) :=
begin
  rw [homogenous_submodule_eq_finsupp_supported, finsupp.supported_eq_span_single],
  refl,
end
#print submodule.span_induction

@[elab_as_eliminator, elab_strategy]
theorem submodule.span_induction {R : Type*} {M : Type*} [_inst_1 : semiring R]
  [_inst_2 : add_comm_monoid M] [_inst_5 : module R M] {x : M}
  {s : set M} {p : M → Prop}
  (hx : x ∈ submodule.span R s)
  (h0 : p 0)
  (hadd : ∀ (a : R) (x y : M), x ∈ s → y ∈ submodule.span R s → p y → p (a • x + y)) : p x :=
sorry

lemma is_homogeneous.induction_on'
  {p : mv_polynomial σ R → Prop}
  (hmonomial : ∀ d r, p (monomial d r))
  (hadd : ∀ j (a b : mv_polynomial σ R),
    a.is_homogeneous j → b.is_homogeneous j → p a → p b → p (a + b))
  {x : mv_polynomial σ R} {i : ℕ} (hx : x.is_homogeneous i)
  : p x :=
begin
  let p_submonoid : add_submonoid (mv_polynomial σ R) :=
  { carrier := { x | x.is_homogeneous i ∧ p x },
    add_mem' := λ a b ⟨ha, pa⟩ ⟨hb, pb⟩, ⟨ha.add hb, hadd i a b ha hb pa pb⟩,
    zero_mem' := ⟨is_homogeneous_zero _ _ _, by simpa using hmonomial 0 0⟩ },
  suffices : x ∈ p_submonoid, { exact and.right this },
  rw ←finsupp.sum_single x,
  apply add_submonoid.finsupp_sum_mem,
  intros d hd,
  exact ⟨is_homogeneous_monomial _ _ _ (hx hd), hmonomial _ _⟩,
end



#print submodule.span_induction
/-- To prove a property `p` on all homogenous polynomials, it suffices to prove it for monomials
and their summations. -/
lemma is_homogeneous.induction_on'
  {p : mv_polynomial σ R → Prop}
  (hmonomial : ∀ d r, p (monomial d r))
  (hadd : ∀ j (a b : mv_polynomial σ R), a.is_homogeneous j → b.is_homogeneous j → p a → p b → p (a + b))
  {x : mv_polynomial σ R} {i : ℕ} (hx : x.is_homogeneous i)
  : p x :=
begin
  rw [←mem_homogeneous_submodule, homogeneous_submodule_eq_span_monomial] at hx,
  suffices : p x ∧ x.is_homogeneous i,
  { exact this.1 },
  apply submodule.span_induction hx,
  { rintros xi ⟨d, hd, rfl⟩,
    admit },
  { admit },
  sorry, --oops
  sorry, --oops
end

end mv_polynomial

end mv_polynomial

#exit

eval main


import order.complete_lattice
import data.set.intervals.basic
import data.fin

open set



example {X : Type*} [partial_order X] (x y : X) :
  (Ico y x = {y}) ↔ (∀ z, y < z ↔ x ≤ z) :=
begin
  simp only [set.eq_singleton_iff_unique_mem,
    set.mem_Ico, le_refl, true_and, and_imp],
  split,
  { assume h z,
    split,
    { assume hyz,
      have := h.2 z (le_of_lt hyz),
      admit
       },
    { assume hxz,
      refine lt_of_le_of_ne _ _,
      {  } }
     }


end


universe u

open set

variables (X : Type u) [complete_lattice X]

structure composition_series : Type u :=
(length : ℕ)
(series : fin length.succ → X)
-- (zero : series 0 = ⊥)
-- (last : series (fin.last length) = ⊤)
(step : ∀ i : fin length, Ico (series i.cast_succ) (series i.succ) = {series i.cast_succ})

-- /- Make composition series a list on an interval -/
-- #print list.chain'
-- structure composition_series' : Type u :=
-- (l : list X)
-- ()

namespace composition_series

instance : has_coe_to_fun (composition_series X) :=
{ F := _, coe := composition_series.series }

variables {X}

theorem lt_succ (s : composition_series X) (i : fin s.length) :
  s i.cast_succ < s i.succ :=
(mem_Ico.1 (eq_singleton_iff_unique_mem.1 (s.step i)).1).2

protected theorem strict_mono (s : composition_series X) : strict_mono s :=
fin.strict_mono_iff_lt_succ.2 (λ i h, s.lt_succ ⟨i, nat.lt_of_succ_lt_succ h⟩)

protected theorem injective (s : composition_series X) : function.injective s :=
s.strict_mono.injective

@[simp] protected theorem eq_iff (s : composition_series X) {i j : fin s.length.succ} :
  s i = s j ↔ i = j :=
s.injective.eq_iff

@[simps] def erase_top (s : composition_series X) : composition_series X :=
{ length := s.length - 1,
  series := λ i, s ⟨i, lt_of_lt_of_le i.2 (nat.succ_le_succ (nat.sub_le_self _ _))⟩,
  step := λ i, begin
    have := s.step ⟨i, lt_of_lt_of_le i.2 (nat.sub_le_self _ _)⟩,
    cases i,
    exact this
  end }

def fin.cast_add_right {}

@[simps] def append (s₁ s₂ : composition_series X)
  (h : s₁ (fin.last _) = s₂ 0) : composition_series X :=
{ length := s₁.length + s₂.length,
  series := fin.append (nat.add_succ _ _).symm (s₁ ∘ fin.cast_succ) s₂,
  step := λ i, begin


  end }


lemma last_erase_top (s : composition_series X) :
  s.erase_top (fin.last _) = s (fin.cast_succ (fin.last (s.length - 1))) :=
show s _ = s _, from congr_arg s
begin
  ext,
  simp only [erase_top_length, fin.coe_last, fin.coe_cast_succ, fin.coe_of_nat_eq_mod,
    fin.coe_mk, coe_coe],
  rw [nat.mod_eq_of_lt (lt_of_le_of_lt (nat.sub_le_self _ _) (nat.lt_succ_self _))],
end

-- theorem subsingleton_iff_length_eq_zero (s : composition_series X) :
--   subsingleton X ↔ s.length = 0 :=
-- begin
--   erw [← subsingleton_iff_bot_eq_top, ← s.zero, ← s.last, s.eq_iff, fin.ext_iff],
--   simp [eq_comm]
-- end

variables (r : (X × X) → (X × X) → Prop)

def equivalence (s₁ s₂ : composition_series X) : Type* :=
{ f : fin s₁.length ≃ fin s₂.length //
  ∀ i : fin s₁.length, r (s₁ i, s₁ i.succ) (s₂ (f i), s₂ (f i).succ) }

namespace equivalence

variables [is_equiv _ r]

@[refl] def refl (s : composition_series X) : equivalence r s s :=
⟨equiv.refl _, λ _, is_refl.reflexive _⟩

@[symm] def symm {s₁ s₂ : composition_series X} (h : equivalence r s₁ s₂) :
  equivalence r s₂ s₁ :=
⟨h.1.symm, λ i, is_symm.symm _ _ (by simpa using h.2 (h.1.symm i))⟩

@[trans] def trans {s₁ s₂ s₃ : composition_series X}
  (h₁ : equivalence r s₁ s₂)
  (h₂ : equivalence r s₂ s₃) :
  equivalence r s₁ s₃ :=
⟨h₁.1.trans h₂.1, λ i, is_trans.trans _ _ _ (h₁.2 i) (h₂.2 (h₁.1 i))⟩

lemma append

end equivalence

@[elab_as_eliminator, elab_strategy]
def fin.last_cases {n : ℕ} {C : fin n.succ → Sort*}
  (hlast : C (fin.last n)) (hcast : (Π (i : fin n), C i.cast_succ)) (i : fin n.succ) : C i :=
if hi : i = fin.last _
then cast (by rw hi) hlast
else have hi : i = fin.cast_succ ⟨i, lt_of_le_of_ne (nat.le_of_lt_succ i.2)
    (λ h, hi (fin.ext h))⟩, from fin.ext rfl,
  cast (by rw hi) (hcast _)

@[simp] lemma fin.last_cases_last  {n : ℕ} {C : fin n.succ → Sort*}
  (hlast : C (fin.last n)) (hcast : (Π (i : fin n), C i.cast_succ)) :
  (fin.last_cases hlast hcast (fin.last n): C (fin.last n)) = hlast :=
by simp [fin.last_cases]

@[simp] lemma fin.last_cases_cast_succ  {n : ℕ} {C : fin n.succ → Sort*}
  (hlast : C (fin.last n)) (hcast : (Π (i : fin n), C i.cast_succ)) (i : fin n) :
  (fin.last_cases hlast hcast (fin.cast_succ i): C (fin.cast_succ i)) = hcast i :=
begin
  simp only [fin.last_cases, dif_neg (ne_of_lt (fin.cast_succ_lt_last i)), cast_eq],
  congr,
  simp,
end

lemma equivalent_of_erase_top_equivalent {s₁ s₂ : composition_series X}
  (h0₁ : 0 < s₁.length) (h0₂ : 0 < s₂.length)
  (htop : s₁ (fin.last _) = s₂ (fin.last _))
  (h : equivalence r s₁.erase_top s₂.erase_top)
  (htop_erase_top : s₁.erase_top (fin.last _) = s₂.erase_top (fin.last _)) :
  equivalence r s₁ s₂ :=
let f : fin (s₁.length - 1) ≃ fin (s₂.length - 1) :=
⟨_,
  begin
    intros i j hij,
    refine fin.last_cases _ _ j,

  end⟩

theorem jordan_hoelder (s₁ s₂ : composition_series X)
  (h0 : s₁ 0 = s₂ 0) (hl : s₁ (fin.last _) = s₂ (fin.last _))
  : equivalent r s₁ s₂ :=
begin
  induction hl : s₁.length with n ih generalizing s₁ s₂,
  { admit
    --  haveI hs : subsingleton X,
    -- { rw [subsingleton_iff_length_eq_zero, hl] },
    -- have : s₁.length = s₂.length,
    -- { rw [hl, eq_comm, ← subsingleton_iff_length_eq_zero,
    --     s₁.subsingleton_iff_length_eq_zero, hl] },
    -- use this,
    -- intros i j hij,
    -- have : ∀ x : X, x = s₁ i, from λ _, subsingleton.elim _ _,
    -- rw [this (s₁ j), this (s₂ _), this (s₂ _)],
    -- exact is_refl.reflexive _
    },
  { let H := s₁.erase_top (fin.last _),
    let K := s₂.erase_top (fin.last _),
    by_cases hHK : H = K,
    {  }

      }

end

  -- (second_iso : ∀ h k, r (h ⊔ k, k) (h, h ⊓ k))
  -- (hIco : ∀ g h k : X, Ico h g = {h} → Ico k g = {k} → Ico (h ⊓ k) h = {h ⊓ k})



#exit
import algebra.char_p.basic
import tactic.ring

variables {R : Type} [comm_ring R] [char_p R 7]

@[simp] lemma ring_char_eq : ring_char R = 7 :=
eq.symm $ ring_char.eq _ (by assumption)

@[simp] lemma seven_eq_zero : (7 : R) = 0 :=
calc (7 : R) = (7 : ℕ) : by simp
... = 0 : char_p.cast_eq_zero _ _

@[simp] lemma bit0bit0bit0 (n : R) : (bit0 $ bit0 $ bit0 n) = n :=
calc (bit0 $ bit0 $ bit0 n) = 7 * n + n : by delta bit0; ring
... = n : by simp

@[simp] lemma bit0bit0bit1 (n : R) : (bit0 $ bit0 $ bit1 n) = n + 4 :=
calc (bit0 $ bit0 $ bit1 n) = 7 * n + n + 4 : by delta bit0 bit1; ring
... = _ : by simp

@[simp] lemma bit0bit1bit0 (n : R) : (bit0 $ bit1 $ bit0 n) = n + 2 :=
calc (bit0 $ bit1 $ bit0 n) = 7 * n + n + 2 : by delta bit0 bit1; ring
... = _ : by simp

@[simp] lemma bit0bit1bit1 (n : R) : (bit0 $ bit1 $ bit1 n) = n + 6 :=
calc (bit0 $ bit1 $ bit1 n) = 7 * n + n + 6 : by delta bit0 bit1; ring
... = _ : by simp

@[simp] lemma bit1bit0bit0 (n : R) : (bit1 $ bit0 $ bit0 n) = n + 1 :=
calc (bit1 $ bit0 $ bit0 n) = 7 * n + n + 1 : by delta bit0 bit1; ring
... = _ : by simp

@[simp] lemma bit1bit0bit1 (n : R) : (bit1 $ bit0 $ bit1 n) = n + 5 :=
calc (bit1 $ bit0 $ bit1 n) = 7 * n + n + 5 : by delta bit0 bit1; ring
... = _ : by simp

@[simp] lemma bit1bit1bit0 (n : R) : (bit1 $ bit1 $ bit0 n) = n + 3 :=
calc (bit1 $ bit1 $ bit0 n) = 7 * n + n + 3 : by delta bit0 bit1; ring
... = _ : by simp

@[simp] lemma bit1bit1bit1 (n : R) : (bit1 $ bit1 $ bit1 n) = n :=
calc (bit1 $ bit1 $ bit1 n) = 7 * n + n + 7: by delta bit0 bit1; ring
... = _ : by simp

@[simp] lemma bit0_add_bit0 (n m : R) : bit0 n + bit0 m = bit0 (n + m) :=
by delta bit0 bit1; ring

@[simp] lemma bit0_add_bit1 (n m : R) : bit0 n + bit1 m = bit1 (n + m) :=
by delta bit0 bit1; ring

@[simp] lemma bit1_add_bit0 (n m : R) : bit1 n + bit0 m = bit1 (n + m) :=
by delta bit0 bit1; ring

@[simp] lemma bit1_add_bit1 (n m : R) : bit1 n + bit1 m = bit1 (n + m) + 1 :=
by delta bit0 bit1; ring

@[simp] lemma bit0_add_one (n : R) : bit0 n + 1 = bit1 n :=
by delta bit0 bit1; ring

@[simp] lemma three_add_one : (3 : R) + 1 = 4 :=
by delta bit0 bit1; ring

@[simp] lemma one_add_one : (1 : R) + 1 = 2 :=
by delta bit0 bit1; ring

@[simp] lemma bit1bit0_add_one (n : R) : bit1 (bit0 n) + 1 = bit0 (bit1 n) :=
by delta bit0 bit1; ring

@[simp] lemma bit1bit1_add_one (n : R) : bit1 (bit1 n) + 1 = bit0 (bit0 (n + 1)) :=
by delta bit0 bit1; ring

@[simp] lemma one_add_bit0 (n : R) : 1 + bit0 n = bit1 n :=
by delta bit0 bit1; ring

@[simp] lemma one_add_bit1bit0 (n : R) : 1 + bit1 (bit0 n) = bit0 (bit1 n) :=
by delta bit0 bit1; ring

@[simp] lemma one_add_bit1bit1 (n : R) : 1 + bit1 (bit1 n) = bit0 (bit0 (n + 1)) :=
by delta bit0 bit1; ring

@[simp] lemma one_add_three : (1 : R) + 3 = 4 :=
by delta bit0 bit1; ring

set_option trace.simplify.rewrite true
example : (145903 : R) = 2 :=
begin
  simp,

end

#exit
import group_theory.perm.cycles

open string equiv.perm tactic equiv

run_cmd
do
   "c[1, 4, 3, 2]" ← pure (repr (1 : ℕ)),
   pure ()

variables {A : Type*} [add_comm_group A] (n m k : ℤ) (a b c : A)

example : (n + m) • a = n • a + m • a :=
by abel -- fails

example : (5 : ℤ) • a + a = (6 : ℤ) • a :=
by abel -- works

example : (5 : ℤ) • a + a = (6 : ℕ) • a :=
by abel -- fails

example : (5 + 4 : ℤ) • a + a = (10 : ℤ) • a :=
by abel -- works

example : (5 + 3 + 1 : ℤ) • a + a = (10 : ℤ) • a :=
by abel -- works

#print norm_num.eval_field

#exit
import data.list.basic

variables {A : Type} (op : A → A → A)

#reduce
  let x : ℕ := (list.range 10000).nth_le 0 sorry in
  1
#exit
import group_theory.subgroup
import group_theory.free_group

universes u v

def fintype' : Type* → Type* := id

def fintype'.card {α : Type u} [fintype' α] : Type u := α
set_option pp.universes true



variables {G : Type u} [group G]

def X : has_coe_to_sort (subgroup G) := by apply_instance

#print set_like.has_coe_to_sort

@[simp, to_additive] lemma card_bot {h : fintype' (⊤ : subgroup G)} : ℕ :=
0

#exit

import data.nat.totient
import data.zmod.basic
import group_theory.order_of_element

lemma pow_eq_pow_mod_card {G : Type*} [group G] [fintype G] (a : G) (n : ℕ) :
  a ^ n = a ^ (n % fintype.card G) :=
by rw [pow_eq_mod_order_of, @pow_eq_mod_order_of _ _ _ (_ % fintype.card G),
    nat.mod_mod_of_dvd _ order_of_dvd_card_univ]

lemma pow_eq_pow_mod_totient {n : ℕ} (a : units (zmod n)) (k : ℕ) :
  a ^ k = a ^ (k % nat.totient n) :=
if hn0 : n = 0
  then by simp [hn0]
  else by { haveI : fact (0 < n) := fact.mk (nat.pos_of_ne_zero hn0),
    rw [pow_eq_pow_mod_card a k, zmod.card_units_eq_totient] }

lemma pow_mod_eq_pow_mod_totient {n : ℕ} (a k : ℕ) (han : nat.coprime a n) :
  (a ^ k) % n = (a ^ (k % nat.totient n)) % n :=
(zmod.eq_iff_modeq_nat n).1 begin
  rw [nat.cast_pow, nat.cast_pow, ← zmod.coe_unit_of_coprime a han,
    ← units.coe_pow, ← units.coe_pow, pow_eq_pow_mod_totient],
end

lemma nat.totient_eq_list_range (n : ℕ) :
  nat.totient n = ((list.range n).filter (nat.coprime n)).length :=
begin
  rw [nat.totient, ← list.erase_dup_eq_self.2 (list.nodup_filter _ (list.nodup_range n)),
    ← list.card_to_finset],
  refine congr_arg finset.card _,
  ext,
  simp,
end

def prod_zmod_one_equiv (R : Type*) [semiring R] : R ≃+* R × zmod 1 :=
{ to_fun := λ x, (x, 0),
  inv_fun := prod.fst,
  map_add' := by intros; ext; simp; congr,
  map_mul' := by intros; ext; simp; congr,
  left_inv := λ x, rfl,
  right_inv := λ x, by apply prod.ext; simp; congr }

def zmod_one_prod_equiv (R : Type*) [semiring R] : R ≃+* zmod 1 × R :=
{ to_fun := λ x, (0, x),
  inv_fun := prod.snd,
  map_add' := by intros; ext; simp; congr,
  map_mul' := by intros; ext; simp; congr,
  left_inv := λ x, rfl,
  right_inv := λ x, by apply prod.ext; simp; congr }

local attribute [instance] zmod.char_p

def chinese_remainder (m n : ℕ) (h : m.coprime n) :
  zmod (m * n) ≃+* zmod m × zmod n :=
if hmn0 : m * n = 0
  then if hm1 : m = 1
    then begin
      rw [hm1, one_mul],
      exact zmod_one_prod_equiv _
    end
  else have hn1 : n = 1,
      begin
        rw [nat.mul_eq_zero] at hmn0,
        rcases hmn0 with ⟨rfl, rfl⟩;
        simp [*, fact_iff] at *,
      end,
    begin
      rw [hn1, mul_one],
      exact prod_zmod_one_equiv _
    end
else
by haveI : fact (0 < (m * n)) := fact.mk (nat.pos_of_ne_zero hmn0);
   haveI : fact (0 < m) := fact.mk (nat.pos_of_ne_zero $ λ h, by simp [fact_iff, *] at *);
   haveI : fact (0 < n) := fact.mk (nat.pos_of_ne_zero $ λ h, by simp [fact_iff, *] at *);
exact
{ to_fun := λ x, (zmod.cast_hom (dvd_mul_right _ _) _ x, zmod.cast_hom (dvd_mul_left _ _) _ x),
  inv_fun := λ x, nat.modeq.chinese_remainder h x.1.val x.2.val,
  map_mul' := λ _ _, by ext; simp only [ring_hom.map_mul]; refl,
  map_add' := λ _ _, by ext; simp only [ring_hom.map_add]; refl,
  left_inv := λ x, begin
    conv_rhs { rw ← zmod.nat_cast_zmod_val x },
    dsimp,
    rw [zmod.eq_iff_modeq_nat, ← nat.modeq.modeq_and_modeq_iff_modeq_mul h],
    refine
      ⟨(subtype.property (nat.modeq.chinese_remainder h (x : zmod m).val (x : zmod n).val)).1.trans _,
       (subtype.property (nat.modeq.chinese_remainder h (x : zmod m).val (x : zmod n).val)).2.trans _⟩,
    rw [← zmod.eq_iff_modeq_nat, zmod.nat_cast_zmod_val, zmod.nat_cast_val],
    rw [← zmod.eq_iff_modeq_nat, zmod.nat_cast_zmod_val, zmod.nat_cast_val],
  end,
  right_inv := λ x,
    begin
      haveI : fact (0 < (m * n)) := fact.mk (nat.pos_of_ne_zero hmn0),
      haveI : fact (0 < m) := fact.mk (nat.pos_of_ne_zero $ λ h, by simp [fact_iff, *] at *),
      haveI : fact (0 < n) := fact.mk (nat.pos_of_ne_zero $ λ h, by simp [fact_iff, *] at *),
      ext,
      { conv_rhs { rw ← zmod.nat_cast_zmod_val x.1 },
        dsimp,
        rw [@zmod.cast_nat_cast _ (zmod m) _ _ _ (dvd_mul_right _ _)],
        rw [zmod.eq_iff_modeq_nat],
        exact (nat.modeq.chinese_remainder h _ _).2.1,
        apply_instance },
      { conv_rhs { rw ← zmod.nat_cast_zmod_val x.2 },
        dsimp,
        rw [@zmod.cast_nat_cast _ (zmod n) _ _ _ (dvd_mul_left _ _)],
        rw [zmod.eq_iff_modeq_nat],
        exact (nat.modeq.chinese_remainder h _ _).2.2,
        apply_instance }
    end }

lemma totient_mul (m n : ℕ) (h : m.coprime n) : nat.totient (m * n) =
  nat.totient m * nat.totient n :=
if hmn0 : m * n = 0
  then by finish
  else
  begin
    haveI : fact (0 < m * n) := fact.mk (nat.pos_of_ne_zero hmn0),
    haveI : fact (0 < m) := fact.mk (nat.pos_of_ne_zero $ λ h, by simp [fact_iff, *] at *),
    haveI : fact (0 < n) := fact.mk (nat.pos_of_ne_zero $ λ h, by simp [fact_iff, *] at *),
    rw [← zmod.card_units_eq_totient, ← zmod.card_units_eq_totient,
      ← zmod.card_units_eq_totient],
    rw [fintype.card_congr (units.map_equiv (chinese_remainder _ _ h).to_mul_equiv).to_equiv],
    rw [fintype.card_congr (@mul_equiv.prod_units (zmod m) (zmod n) _ _).to_equiv],
    rw [fintype.card_prod]
  end

lemma nat.coprime_pow_left_iff (a b : ℕ) {n : ℕ} (hn : 0 < n) :
  nat.coprime (a ^ n) b ↔ nat.coprime a b :=
begin
  cases n with n,
  { exact (lt_irrefl _ hn).elim },
  { rw [pow_succ, nat.coprime_mul_iff_left],
    exact iff.intro and.left (λ hab, ⟨hab, nat.coprime.pow_left _ hab⟩) }
end

lemma totient_prime_pow {p : ℕ} (hp : p.prime) (n : ℕ) :
  nat.totient (p ^ (n + 1)) = p ^ n * (p - 1) :=
calc nat.totient (p ^ (n + 1))
    = ((finset.range (p ^ (n + 1))).filter (nat.coprime (p ^ (n + 1)))).card : rfl
... = (finset.range (p ^ (n + 1)) \ ((finset.range (p ^ n)).image (* p))).card :
  congr_arg finset.card begin
    rw [finset.sdiff_eq_filter],
    apply finset.filter_congr,
    simp only [finset.mem_range, finset.mem_filter, nat.coprime_pow_left_iff _ _ (nat.succ_pos n),
      finset.mem_image, not_exists, hp.coprime_iff_not_dvd],
    intros a ha,
    split,
    { rintros hap b _ rfl,
      exact hap (dvd_mul_left _ _) },
    { rintros h ⟨b, rfl⟩,
      rw [pow_succ] at ha,
      exact h b (lt_of_mul_lt_mul_left ha (nat.zero_le _)) (mul_comm _ _) }
  end
... = _ :
have h1 : set.inj_on (* p) (finset.range (p ^ n)),
  from λ x _ y _, (nat.mul_left_inj hp.pos).1,
have h2 : (finset.range (p ^ n)).image (* p) ⊆ finset.range (p ^ (n + 1)),
  from λ a, begin
    simp only [finset.mem_image, finset.mem_range, exists_imp_distrib],
    rintros b h rfl,
    rw [pow_succ'],
    exact (mul_lt_mul_right hp.pos).2 h
  end,
begin
  rw [finset.card_sdiff h2, finset.card_image_of_inj_on h1, finset.card_range,
    finset.card_range, ← one_mul (p ^ n), pow_succ, ← nat.mul_sub_right_distrib,
    one_mul, mul_comm]
end

lemma totient_prime {p : ℕ} (hp : p.prime) : nat.totient p = p - 1 :=
by conv_lhs { rw [← pow_one p, totient_prime_pow hp, pow_zero, one_mul] }

namespace tactic.interactive

meta def totient_tac : tactic unit :=
`[simp only [nat.totient_eq_list_range],
  delta nat.coprime,
  dsimp only [list.range, list.range_core],
  dsimp only [list.filter],
  norm_num]

end tactic.interactive

lemma totient_1000000 : nat.totient 1000000 = 400000 :=
calc nat.totient 1000000 = nat.totient (5 ^ 6 * 2 ^ 6) :
  congr_arg nat.totient (by norm_num)
... = 400000 : begin
  rw [totient_mul, totient_prime_pow, totient_prime_pow];
  try {delta nat.coprime}; norm_num
end

lemma totient_400000 : nat.totient 400000 = 160000 :=
calc nat.totient 400000 = nat.totient (2 ^ 7 * 5 ^ 5) :
  congr_arg nat.totient (by norm_num)
... = 160000 : begin
  rw [totient_mul, totient_prime_pow, totient_prime_pow];
  try {delta nat.coprime}; norm_num
end

lemma totient_160000 : nat.totient 160000 = 64000 :=
calc nat.totient 160000 = nat.totient (2 ^ 8 * 5 ^ 4) :
  congr_arg nat.totient (by norm_num)
... = 64000 : begin
  rw [totient_mul, totient_prime_pow, totient_prime_pow];
  try {delta nat.coprime}; norm_num,
end

lemma totient_64000 : nat.totient 64000 = 25600 :=
calc nat.totient 64000 = nat.totient (2 ^ 9 * 5 ^ 3) :
  congr_arg nat.totient (by norm_num)
... = 25600 :
begin
  rw [totient_mul, totient_prime_pow, totient_prime_pow];
  try {delta nat.coprime}; norm_num,
end

lemma totient_25600 : nat.totient 25600 = 10240 :=
calc nat.totient 25600 = nat.totient (2 ^ 10 * 5 ^ 2) :
  congr_arg nat.totient (by norm_num)
... = 10240 :
begin
  rw [totient_mul, totient_prime_pow, totient_prime_pow];
  try {delta nat.coprime}; norm_num,
end

lemma totient_10240 : nat.totient 10240 = 4096 :=
calc nat.totient 10240 = nat.totient (2 ^ 11 * 5) :
  congr_arg nat.totient (by norm_num)
... = 4096 :
begin
  rw [totient_mul, totient_prime_pow, totient_prime];
  try {delta nat.coprime}; norm_num,
end

def pow_mod (a b c : ℕ) : ℕ := (a ^ b) % c

lemma pow_mod_bit0 (a b c : ℕ) :
  pow_mod a (bit0 b) c = pow_mod a b c ^ 2 % c :=
by rw [pow_mod, pow_mod, pow_two, bit0, pow_add, nat.mul_mod],

lemma pow_mod_bit1 (a b c : ℕ) :
  pow_mod a (bit1 b) c = (pow_mod a b c ^ 2 % c * a % c) % c :=
begin
  rw [bit1, bit0, pow_mod, pow_add, ← pow_mod, nat.mul_mod, ← pow_mod,
    ← bit0, pow_mod_bit0, pow_one, nat.mod_mod, pow_mod, pow_mod],
  conv_rhs { rw nat.mul_mod },
  rw [nat.mod_mod]
end

lemma pow_mod_one (a c : ℕ) :
  pow_mod a 1 c = a % c :=
by simp [pow_mod]

def seven_sevens_mod : (7 ^ 7 ^ 7 ^ 7 ^ 7 ^ 7 ^ 7) % 1000000 = 172343 :=
begin
  rw [pow_mod_eq_pow_mod_totient, totient_1000000,
      @pow_mod_eq_pow_mod_totient 400000, totient_400000,
      @pow_mod_eq_pow_mod_totient 160000, totient_160000,
      @pow_mod_eq_pow_mod_totient 64000, totient_64000,
      @pow_mod_eq_pow_mod_totient 25600, totient_25600,
      @pow_mod_eq_pow_mod_totient 10240, totient_10240],
  repeat { rw [← pow_mod] },
  norm_num [pow_mod_bit0, pow_mod_bit1, pow_mod_one],
  all_goals { delta nat.coprime, norm_num }
end


#print axioms seven_sevens_mod

#exit

import data.nat.fib
import data.real.sqrt
import tactic

open nat real

lemma fib_formula : ∀ n : ℕ,
  (((1 + real.sqrt 5) / 2) ^ n - ((1 - sqrt 5) / 2) ^ n) / sqrt 5 = fib n
| 0     := by simp
| 1     := begin
  have hs : real.sqrt 5 ≠ 0, by norm_num,
  field_simp [hs],
  ring,
end
| (n+2) := begin
  have hs : real.sqrt 5 ≠ 0, { norm_num },
  have hsq : real.sqrt 5 ^ 2 = 5, { norm_num },
  have hsq3 : real.sqrt 5 ^ 3 = real.sqrt 5 * 5, { rw [pow_succ, hsq] },
  have hsq4 : real.sqrt 5 ^ 4 = 1 + 24 - 1 + 5 - 4, { rw [pow_bit0, hsq], norm_num },
  rw [fib_succ_succ, nat.cast_add, ← fib_formula, ← fib_formula],
  field_simp [hs],
  ring_exp,
  rw [hsq, hsq3, hsq4],
  ring
end

#exit
import data.int.basic

inductive poly
| C : ℤ → poly
| X : poly
| add : poly → poly → poly
| mul : poly → poly → poly

open poly

instance : has_add poly := ⟨poly.add⟩
instance : has_mul poly := ⟨poly.mul⟩
instance : has_one poly := ⟨C 1⟩
instance : has_zero poly := ⟨C 0⟩
instance : has_coe ℤ poly := ⟨C⟩
instance : has_pow poly ℕ := ⟨λ p n, nat.rec_on n 1 (λ n q, nat.cases_on n p (λ m, p * q))⟩

/-- Remove leading zeroes from a list -/
def erase_zeroes : list ℤ → list ℤ
| [] := []
| m@(a :: l) := if a = 0 then erase_zeroes l else m

-- add_list_aux l₁ l₂ r returns ((reverse l₁ + reverse l₂) ++ r)
def add_list_aux :
  list ℤ →
  list ℤ →
  list ℤ →
  list ℤ
| [] [] r := r
| (a::l) [] r := add_list_aux l [] (a::r)
| [] (a::l) r := add_list_aux [] l (a::r)
| (a::l₁) (b::l₂) r := add_list_aux l₁ l₂ ((a + b) :: r)

def add_list (l₁ l₂ : list ℤ) :=
erase_zeroes (add_list_aux l₁.reverse l₂.reverse [])

def mul_list : list ℤ → list ℤ → list ℤ
| [] l       := []
| (a::l₁) l₂ :=
  add_list (l₂.map (*a) ++ list.repeat 0 l₁.length) (mul_list l₁ l₂)

def poly_to_list : poly → list ℤ
| (C n) := if n = 0 then [] else [n]
| X     := [1, 0]
| (add p q) := add_list (poly_to_list p) (poly_to_list q)
| (mul p q) := mul_list (poly_to_list p) (poly_to_list q)

instance : has_repr poly := ⟨repr ∘ poly_to_list⟩

/- Multiples of (X - a) form an ideal -/

def mults_is_ideal_zero (a : ℤ) : poly × poly := (0, 0)

def mults_is_ideal_add (a : ℤ) (f fdiv g gdiv : poly) : poly × poly :=
(f + g, fdiv + gdiv)

def mults_is_ideal_smul (a : ℤ) (f g gdiv : poly) : poly × poly :=
(f * g, f * gdiv)

def ring_hom_well_defined_on_quotient
  (I : poly → Type) (I0 : I 0)
  (Iadd : Π p q, I p → I q → I (p + q))
  (Ismul : Π p q, I q → I (p * q))


def mod_div (a : ℤ) : poly → ℤ × poly
| (C n)     := (n, 0)
| X         := (a, 1)
| (add p q) :=
  let (np, Pp) := mod_div p in
  let (nq, Pq) := mod_div q in
  -- p = Pp * (X - a) + np
  -- q = Pq * (X - a) + nq
  -- So p + q = (Pp + Pq) * (X - a) + (np + nq)
  (np + nq, Pp + Pq)
| (mul p q) :=
  let (np, Pp) := mod_div p in
  let (nq, Pq) := mod_div q in
  -- p = Pp * (X - a) + np
  -- q = Pq * (X - a) + nq
  -- p * q = (Pp * Pq * (X - a) + np * Pq + nq * Pp) * (X - a) + (np + nq)
  (np + nq, Pp * Pq * (X + C (-a)) + np * Pq + nq * Pp)

#eval mod_div (-1) (X * X + 2 * X + 1)


#exit
import data.list.perm

variables {α : Type*} [decidable_eq α] {l₁ l₂ : list α}
#eval list.permutations [1,2,3,0]

lemma X {α : Type} (a : α) (l : list α) : list.permutations (l ++ [a]) =
  l.permutations.bind (λ l, (list.range l.length.succ).map (λ n, l.insert_nth n a)) := sorry
#print list.permutations_aux2

lemma permutations_cons {α : Type} (a : α) (l : list α) :
  list.permutations (a :: l) ~ l.permutations.bind
  (λ l, (list.range l.length.succ).map (λ n, l.insert_nth n a)) :=
begin
  unfold list.permutations,

end


#eval let l := [1,2,3] in let a := 0 in
(list.permutations (l ++ [a]) =
  l.permutations.bind (λ l, (list.range l.length.succ).map (λ n, l.insert_nth n a)) : bool)


#exit
ariables (P : Prop) (R : P → P → Prop) (α : Type) (f : P → α)
  (H : ∀ x y, R x y → f x = f y) (q : quot R) (h : P)

example : q = quot.mk R h := rfl
#print task
#print task.

local attribute [semireducible] reflected
run_cmd tactic.add_decl (declaration.thm `exmpl []

  `(∀ (P : Prop) (R : P → P → Prop) (α : Type) (f : P → α)
    (H : ∀ x y, R x y → f x = f y) (q : quot R) (h : P),
    quot.lift f H q = quot.lift f H (quot.mk R h))
  (task.pure `(λ (P : Prop) (R : P → P → Prop) (α : Type) (f : P → α)
    (H : ∀ x y, R x y → f x = f y) (q : quot R) (h : P),
    eq.refl (quot.lift f H q))))

example : quot.lift f H q = quot.lift f H (quot.mk R h) := rfl



#exit
import data.polynomial.field_division
import data.real.liouville



lemma roots_derivative : ∀ (f : polynomial ℝ),
  f.roots.to_finset.card = f.derivative.roots.to_finset.card + 1
| f :=
  if hfe : f.roots.to_finset = ∅
    then by simp [hfe]
    else begin
      cases finset.nonempty_of_ne_empty hfe with a ha,
      have hf0 : f ≠ 0, from λ hf0, by simp * at *,
      rw [multiset.mem_to_finset, mem_roots hf0, ← dvd_iff_is_root] at ha,
      rcases ha with ⟨g, rfl⟩,
      rw [derivative_mul, derivative_sub, derivative_X, derivative_C,
        sub_zero, one_mul, roots_mul hf0, roots_X_sub_C, multiset.to_finset_add],
      simp,


    end





def f (n : ℕ) (h : acc (>) n) : unit :=
acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n)) h

-- notation `t1 ` := f 0 a

-- def t2 (a : acc (>) 0) : unit := acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n)) a

-- def t3 (a : acc (>) 0) : unit := acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n))
--     (acc.inv a (nat.lt_succ_self 0))

example (a : acc (>) 0) :
  f 0 a
  = (acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n)) a : unit) :=
rfl

example (a : acc (>) 0) :
  (acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n))
    (acc.intro 0 (λ y hy, acc.inv a hy)) : unit)
  = acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n))
    (acc.inv a (nat.lt_succ_self 0)) :=
rfl

example (a : acc (>) 0) :
  f 0 a
  = acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n))
    (acc.inv a (nat.lt_succ_self 0)) := rfl



inductive X (a : acc (>) 0) : unit → Type
| mk (u : unit) : X u

example (a : acc (>) 0) :
  X a (f 0 a)
  = X a (acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n)) a : unit) :=
rfl

#check λ a : acc (>) 0, @id
    (X a (acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n))
    (acc.intro 0 (λ y hy, acc.inv a hy))))
    (X.mk (acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n))
    (acc.inv a (nat.lt_succ_self 0))))

#check λ a : acc (>) 0,
    -- @id (X a (f 0 a))
    (@id (X a ((acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n)) a)))
    (X.mk (acc.rec (λ n _ g, g (n + 1) (nat.lt_succ_self n))
      (acc.inv a (nat.lt_succ_self 0)))))



variables {A : Type}

def T (A : Type) : A → A → Prop := λ _ _, true

inductive B : quot (T A) → Type
| mk : Π a : A, B (quot.mk (T A) a)

#print funext

def f (a : quot (T A)) : B a :=
quot.lift (λ x, _) _ a

#exit

import data.complex.basic
open complex


lemma X : (2 : ℂ).im = 0 :=
begin
  simp,
end

#print X

inductive term (L : signature) : ℕ → Type
| Var  (v : L.Variables) : term 0
| Fun {n : ℕ} (f : L.funcs n) : term n
| App {n : ℕ} : term (n+1) → term 0 → term n


open subgroup

variables {G : Type*} {H : Type*} [group G] [group H]

example (p q : Prop) : (p → q) → (¬¬p → ¬¬q) :=
λ h hnp hq, hnp (λ hp, hq $ h hp)

example (p q r : Prop)
  (h : ¬ ((p → q) ↔ r) ↔ (p → (q ↔ r))) : ¬p :=
begin
  by_cases hp : p,
  { simp [hp] at h,
    exact h.elim },
  { assumption }
end

example (p q r : Prop)
  (h : ¬ ((p → q) ↔ r) ↔ (p → (q ↔ r))) : ¬r :=
begin
  by_cases hr : r,
  { by_cases hp : p;
    simp [hp, hr] at h;
    contradiction },
  { assumption }
end

example (p q r : Prop) :
  (¬(((p → q) ↔ r) ↔ (p → (q ↔ r)))) ↔ ¬p ∧ ¬r :=
⟨λ h, ⟨λ hp, h ⟨λ h _, ⟨λ hq, h.1 (λ _, hq), λ hr, h.2 hr hp⟩,
  λ h2, ⟨λ hpq, (h2 hp).1 (hpq hp), λ hr _, (h2 hp).2 hr⟩⟩,
  λ hr, h ⟨λ h2 hp, ⟨λ _, hr, λ _, h2.2 hr hp⟩,
  λ h2, ⟨λ _, hr, λ _ hp, (h2 hp).2 hr⟩⟩⟩,
  λ h h2, h.2 $ (h2.2 (λ hp, (h.1 hp).elim)).1 (λ hp, (h.1 hp).elim)⟩

lemma Z (h : ∀ (p q r : Prop),
  (((p → q) ↔ r) ↔ (p → (q ↔ r))) ↔ p ∨ r) (p : Prop) : p ∨ ¬p  :=
(h p true (¬ p)).1
  ⟨λ h hp, ⟨λ _, h.1 (λ _, trivial), λ _, trivial⟩,
  λ h, ⟨λ _ hp, (h hp).1 trivial hp, λ _ _, trivial⟩⟩

lemma Z1 (h : ∀ (p q r : Prop),
  (((p → q) ↔ r) ↔ (p → (q ↔ r))) ↔ p ∨ r) (p : Prop) : p ∨ ¬p  :=
begin
  have := h (¬ p) false p,
  simp only [true_implies_iff, true_iff, true_or, iff_true, false_iff,
    false_implies_iff, iff_false, false_or, imp_false] at this,
end
#print axioms Z

example : ¬ ((false → true) ↔ false) ↔ (false → (true ↔ false)) :=
begin
  simp,

end

#exit

lemma commutative_of_cyclic_center_quotient [is_cyclic H] (f : G →* H)
  (hf : f.ker ≤ center G) (a b : G) : a * b = b * a :=
begin
  rcases is_cyclic.exists_generator f.range with ⟨⟨x, y, rfl⟩, hx⟩,
  rcases hx ⟨f a, a, rfl⟩ with ⟨m, hm⟩,
  rcases hx ⟨f b, b, rfl⟩ with ⟨n, hn⟩,
  have hm : f y ^ m = f a, by simpa [subtype.ext_iff] using hm,
  have hn : f y ^ n = f b, by simpa [subtype.ext_iff] using hn,
  have ha : y ^ (-m) * a ∈ center G, from hf (f.mem_ker.2 (by group_rel [hm])),
  have hb : y ^ (-n) * b ∈ center G, from hf (f.mem_ker.2 (by group_rel [hn])),
  have this := mem_center_iff.1 ha (y ^ n),
  have that := mem_center_iff.1 hb a,
  group_rel [this, that],
end

#print commutative_of_cyclic_center_quotient
def comm_group_of_cycle_center_quotient [is_cyclic H] (f : G →* H)
  (hf : f.ker ≤ center G) : comm_group G :=
{ mul_comm := commutative_of_cyclic_center_quotient f hf,
  ..show group G, by apply_instance }




#exit
import logic.function.iterate
import tactic

example {G : Type} [group G] (a b : G) :
  (a * b * a⁻¹) * (a * b * a * b^2)⁻¹ * (a * b * a⁻¹)⁻¹ *
  (b⁻¹ * a⁻¹) * (a * b * a * b^2) * (b⁻¹ * a⁻¹)⁻¹ = a * b * a⁻¹ * b⁻¹  :=
begin
  simp [mul_assoc, pow_succ],

end

lemma F {G : Type} [group G] (a b c : G) (ha : a^2 = 1) (hb : b^3 = 1)
  (hr : c * a * c⁻¹ = b) : a = 1 :=
begin
  subst hr,
  simp [pow_succ, mul_assoc] at *,

end


def h : (ℕ → bool) → bool × (ℕ → bool) :=
λ s, (s 0, s ∘ nat.succ)

variables {X : Type} (f : X → bool × X)

def UMP (x : X) (n : ℕ) : bool :=
(f ((prod.snd ∘ f)^[n] x)).1

lemma commutes : h ∘ UMP f = λ x, ((f x).1, (UMP f (f x).2)) :=
begin
  ext,
  { simp [h, UMP] },
  { simp [h, UMP] }
end

lemma uniqueness (W : X → (ℕ → bool)) (hW : ∀ x, h (W x) = ((f x).1, (W (f x).2))) :
  W = UMP f :=
begin
  ext x n,
  unfold UMP h at *,
  simp only [prod.ext_iff, function.funext_iff, function.comp_apply] at hW,
  induction n with n ih generalizing x,
  { simp [(hW x).1] },
  { simp [(hW x).2, ih] }
end

#exit
import data.list.basic

variables {α : Type*}

inductive count_at_least (a : α) : ℕ → list α → Prop
| nil : count_at_least 0 []
| cons_self {n l} : count_at_least n l → count_at_least (n + 1) (a :: l)
| cons {b n l} : count_at_least n l → count_at_least n (b :: l)

inductive duplicate (a : α) : list α → Prop
| cons_mem {l} : a ∈ l → duplicate (a :: l)
| cons_duplicate {b l} : duplicate l → duplicate (b :: l)

#exit
open nat
example (a b : ℕ) (h : succ a = succ b) : a = b :=
show a = @nat.rec (λ n, ℕ) 0 (λ n _, n) (succ b),
from h ▸ rfl

variables
  (formula : Type)
  (T_proves : formula → Prop)
  (is_true : formula → formula)
  (implies : formula → formula → formula)
  (himplies : ∀ {φ ψ}, T_proves (implies φ ψ) → T_proves φ → T_proves ψ)
  (and : formula → formula → formula)
  (handl : ∀ {φ ψ}, T_proves (and φ ψ) → T_proves φ)
  (handr : ∀ {φ ψ}, T_proves (and φ ψ) → T_proves ψ)
  (false : formula)
  (hcons : ¬ T_proves false)
  (h1 : ∀ {φ}, T_proves φ → T_proves (is_true φ))
  (h3 : ∀ {φ}, T_proves (is_true φ) → T_proves φ) -- Need Rosser's trick
  (ρ : formula)
  (hρ : T_proves (and (implies ρ (implies (is_true ρ) false))
    (implies (implies ρ false) (is_true ρ))))

include formula T_proves is_true implies and false h1 h3 ρ hρ

lemma rho_not_is_true : ¬ T_proves ρ :=
assume h : T_proves ρ,
have T_proves_not_is_true_ρ : T_proves (implies (is_true ρ) false),
  from himplies (handl hρ) h,
have T_proves_is_true_ρ : T_proves (is_true ρ),
  from h1 h,
have T_proves_false : T_proves false,
  from himplies T_proves_not_is_true_ρ T_proves_is_true_ρ,
hcons T_proves_false

lemma not_rho_not_is_true : ¬ T_proves (implies ρ false) :=
assume h : T_proves (implies ρ false),
have T_proves_is_true_ρ : T_proves (is_true ρ),
  from himplies (handr hρ) h,
have T_proves_ρ : T_proves ρ,
  from h3 T_proves_is_true_ρ,
have T_proves_false : T_proves false,
  from himplies h T_proves_ρ,
hcons T_proves_false

#reduce not_rho_not_is_true

#exit

#eval quot.unquot ((finset.univ : finset (zmod 3 × zmod 3 × zmod 3)).filter
(λ x: (zmod 3 × zmod 3 × zmod 3), 5 * x.1^2 - 7 * x.2.1^2 + x.2.2 ^ 2 = 0)).1

#exit
#eval let c : ℚ := 1 in let d : ℚ := -2 in
  c * d * (c + d)

example (a b c d : ℝ) (h : 0 < c * d * (c + d)) :
  (a + b)^2 / (c + d) ≤ a^2 / c + b^2 / d :=
sub_nonneg.1 $
  calc 0 ≤ (a * d - b * c) ^ 2 / (c * d * (c + d)) :
    div_nonneg (pow_two_nonneg _) (le_of_lt h)
  ... = _ : begin
    have hc0 : c ≠ 0, from λ h, by simp [*, lt_irrefl] at *,
    have hd0 : d ≠ 0, from λ h, by simp [*, lt_irrefl] at *,
    have hcd0 : c + d ≠ 0, from λ h, by simp [*, lt_irrefl] at *,
    field_simp [hc0, hd0, hcd0],
    ring
  end

#exit
import group_theory.perm.basic
import group_theory.subgroup

open equiv

example (p : Prop) : ¬(¬p ∧ ¬¬p) :=
λ h, h.2 h.1



example (x y z : perm bool)
  (a : subgroup.closure ({(x * y * z)} : set (perm bool)))
  (b : subgroup.closure ({(x * (y * z))} : set (perm bool))) :
  a * a = b * b :=
begin

end


example {G : Type} [group G] (x y z : G)
  (a : subgroup.closure ({(x * y * z)} : set G))
  (b : subgroup.closure ({(x * (y * z))} : set G)) :
  a * a = b * b :=
begin

end




example {A : Type*} (f : set A → A) (h : function.injective f) : false :=
let s := f '' {y | f y ∉ y} in
have h1 : f s ∉ s, from
  λ hs, Exists.rec (λ t ht, ht.1 (eq.rec hs (h ht.2).symm)) hs,
have h2 : f s ∈ s, from ⟨s, h1, eq.refl _⟩,
h1 h2

#print X

#exit
inductive myheq {α : Type} : ∀ {β : Type}, α → β → Type
| refl (a : α) : myheq a a

lemma heq_refl {α} {a b : α} (h : myheq a b) : myheq (myheq.refl a) h :=
  @myheq.rec α (λ α' a a' h', myheq (myheq.refl a) h') (λ a, myheq.refl (myheq.refl a)) α a b h

def myeq {α : Type} (a b : α) : Type := myheq a b

lemma eq_irrel {α} {a b : α} (h₁ h₂ : myeq a b) : myeq h₁ h₂ :=
  @myheq.rec α (λ α a b h₁, ∀ h₂, myeq h₁ h₂) (λ a h₂, heq_refl h₂) α a b h₁ h₂

#exit
import data.list.chain

section monoids

-- given a family of monoids, where both the monoids and the indexing set have decidable equality.
variables {ι : Type*} (G : Π i : ι, Type*) [Π i, monoid (G i)]
  [decidable_eq ι] [∀ i, decidable_eq (G i)]

-- The coproduct of our monoids.
@[derive decidable_eq]
def coprod : Type* := { l : list (Σ i, { g : G i // g ≠ 1 }) // (l.map sigma.fst).chain' (≠) }
variable {G}

-- `w.head_isn't i` says that `i` is not the head of `w`.
def coprod.head_isn't (w : coprod G) (i : ι) : Prop := ∀ p ∈ (w.val.map sigma.fst).head', i ≠ p

section cases
-- here we define a custom eliminator for `coprod`. The idea is we have an index `i`, and
-- want to say that every `w : coprod G` either (1) doesn't have `i` as its head, or (2) is `g * w'`
-- for some `g : G i`, where `w'` doesn't have `i` as its head.
variables {i : ι} {C : coprod G → Sort*}
  (d1 : Π w : coprod G, w.head_isn't i → C w)
  (d2 : Π (w : coprod G) (h : w.head_isn't i) (g), C ⟨⟨i, g⟩ :: w.val, w.property.cons' h⟩)
include d1 d2

def coprod_cases : Π w : coprod G, C w
| w@⟨[], _⟩ := d1 w $ by rintro _ ⟨⟩
| w@⟨⟨j, g⟩ :: ls, h⟩ := if ij : i = j then by { cases ij, exact d2 ⟨ls, h.tail⟩ h.rel_head' g }
else d1 w $ by { rintro _ ⟨⟩ ⟨⟩, exact ij rfl }

variables {d1 d2}

-- computation rule for the first case of our eliminator
lemma beta1 : ∀ (w : coprod G) h, (coprod_cases d1 d2 w : C w) = d1 w h
| ⟨[], _⟩ h := rfl
| ⟨⟨j, g⟩ :: ls, hl⟩ h := by { rw [coprod_cases, dif_neg], exact h j rfl }

-- computation rule for the second case of our eliminator
lemma beta2 (w : coprod G) (h : w.head_isn't i) (g) {x} :
  (coprod_cases d1 d2 ⟨⟨i, g⟩ :: w.val, x⟩ : C ⟨⟨i, g⟩ :: w.val, x⟩) = d2 w h g :=
by { rw [coprod_cases, dif_pos rfl], cases w, refl }

end cases

-- prepend `g : G i` to `w`, assuming `i` is not the head of `w`.
def rcons' {i : ι} (g : G i) (w : coprod G) (h : w.head_isn't i) : coprod G :=
if g_one : g = 1 then w else ⟨⟨i, g, g_one⟩ :: w.val, w.property.cons' h⟩

-- prepend `g : G i` to `w`. NB this is defined in terms of `rcons'`: this will be a recurring theme.
def rcons {i : ι} (g : G i) : coprod G → coprod G :=
coprod_cases (rcons' g) (λ w h g', rcons' (g * ↑g') w h)

-- computation rules for `rcons`
lemma rcons_def1 {i : ι} {g : G i} {w : coprod G} (h) : rcons g w = rcons' g w h := beta1 _ _
lemma rcons_def2 {i : ι} {g : G i} {w : coprod G} (h) (g') {x} :
  rcons g ⟨⟨i, g'⟩ :: w.val, x⟩ = rcons' (g * ↑g') w h := beta2 _ _ _

-- prepending one doesn't change our word
lemma rcons_one {i : ι} : ∀ w : coprod G, rcons (1 : G i) w = w :=
begin
  apply coprod_cases,
  { intros w h, rw [rcons_def1 h, rcons', dif_pos rfl], },
  { rintros w h ⟨g, hg⟩, rw [rcons_def2 h, one_mul, rcons', dif_neg], refl, }
end

-- preliminary for `rcons_mul`
private lemma rcons_mul' {i : ι} {g g' : G i} {w : coprod G} (h : w.head_isn't i) :
  rcons (g * g') w = rcons g (rcons g' w) :=
begin
  rw [rcons_def1 h, rcons_def1 h, rcons', rcons'],
  split_ifs,
  { rw [h_2, mul_one] at h_1, rw [h_1, rcons_one], },
  { rw [rcons_def2 h, rcons', dif_pos], exact h_1, },
  { rw [rcons_def1 h, rcons', dif_neg], { congr, rw [h_2, mul_one], }, simpa [h_2] using h_1, },
  { rw [rcons_def2 h, rcons', dif_neg], refl, },
end

-- we can prepend `g * g'` one element at a time.
lemma rcons_mul {i : ι} (g : G i) (g' : G i) : ∀ w, rcons (g * g') w = rcons g (rcons g' w) :=
begin
  apply coprod_cases,
  { apply rcons_mul', },
  { intros w h g'', rw [rcons_def2 h, rcons_def2 h, mul_assoc,
    ←rcons_def1, rcons_mul' h, ←rcons_def1] }
end

-- Every `G i` thus acts on the coproduct.
@[simps] instance bar (i) : mul_action (G i) (coprod G) :=
{ smul := rcons, one_smul := rcons_one, mul_smul := rcons_mul }

-- Prepending a letter to a word means acting on that word. This will be useful for proofs by
-- induction on words.
lemma cons_as_smul {i} {g} (ls) (hl) :
 (⟨⟨i, g⟩ :: ls, hl⟩ : coprod G) = (g.val • ⟨ls, hl.tail⟩ : coprod G) :=
begin
  rw [bar_to_has_scalar_smul, rcons_def1, rcons', dif_neg g.property],
  { congr, ext, refl, }, { exact hl.rel_head', },
end

section action
-- Given actions of `G i` on `X`, the coproduct also has a scalar action on `X`. We'll use this
-- both to define multiplication in the coproduct, and to get its universal property.
variables {X : Type*} [∀ i, mul_action (G i) X]

instance foo : has_scalar (coprod G) X := ⟨λ g x, g.val.foldr (λ l y, l.snd.val • y) x⟩

-- preliminary for `foobar`.
private lemma foobar' {i} {g : G i} {x : X} {w : coprod G} (h : w.head_isn't i) :
  (rcons g w) • x = g • (w • x) :=
by { rw [rcons_def1 h, rcons'], split_ifs, { rw [h_1, one_smul], }, { refl, }, }

-- (I'm not sure it's worth it to use these typeclasses, since Lean gets a bit confused by them...)
instance foobar (i) : is_scalar_tower (G i) (coprod G) X :=
⟨begin
  intros g' w x, revert w,
  apply coprod_cases,
  { apply foobar', },
  { intros w h g, rw [bar_to_has_scalar_smul, rcons_def2 h, ←rcons_def1 h,
    foobar' h, mul_smul], refl, }
end⟩

end action

instance coprod_monoid : monoid (coprod G) :=
{ mul := λ x y, x • y,
  mul_assoc := begin
    rintros ⟨ls, hl⟩ b c,
    change (_ • _) • _ = _ • (_ • _),
    induction ls with p ls ih,
    { refl, },
    cases p with i g,
    rw [cons_as_smul, smul_assoc g.val _ b, smul_assoc, ih, smul_assoc],
    apply_instance, -- ??
  end,
  one := ⟨[], list.chain'_nil⟩,
  one_mul := λ _, rfl,
  mul_one := begin
    rintro ⟨ls, hl⟩,
    change _ • _ = _,
    induction ls with p ls ih,
    { refl },
    cases p with i g,
    rw [cons_as_smul, smul_assoc, ih],
  end }

def of {i} : G i →* coprod G :=
{ to_fun := λ g, g • 1,
  map_one' := rcons_one _,
  map_mul' := by { intros, change rcons _ _ = _ • _, rw [rcons_mul, smul_assoc], refl } }

lemma cons_as_mul {i} {g} (ls) (h) :
 (⟨⟨i, g⟩ :: ls, h⟩ : coprod G) = (of g.val * ⟨ls, h.tail⟩ : coprod G) :=
by { convert cons_as_smul ls h, change (_ • _) • _ = _, rw smul_assoc g.val, congr, apply_instance }

def ump (X : Type*) [monoid X] :
  (Π {i}, G i →* X) ≃ (coprod G →* X) :=
{ to_fun := λ fi, begin
    letI : ∀ i, mul_action (G i) X := λ i, mul_action.comp_hom _ fi,
    refine { to_fun := λ g, g • 1, map_one' := rfl, map_mul' := _ },
    rintros ⟨ls, hl⟩ b,
    change (_ • _) • _ = _,
    induction ls with p ls ih,
    { exact (one_mul _).symm },
    cases p with i g,
    rw [cons_as_smul, smul_assoc g.val _ b, smul_assoc, ih, smul_assoc],
    { symmetry, apply mul_assoc, },
    { apply_instance },
  end,
  inv_fun := λ f i, f.comp of,
  left_inv := begin
    intro fi, letI : ∀ i, mul_action (G i) X := λ i, mul_action.comp_hom _ fi,
    ext i g, change (g • (1 : coprod G)) • (1 : X) = fi g,
    rw smul_assoc, apply mul_one,
  end,
  right_inv := begin
    intro f,
    ext w,
    cases w with ls hl,
    change _ • 1 = f ⟨ls, hl⟩,
    induction ls with p ls ih,
    { exact f.map_one.symm },
    cases p with i g,
    conv_rhs { rw [cons_as_mul, f.map_mul] },
    letI : ∀ i, mul_action (G i) X := λ i, mul_action.comp_hom _ (f.comp of),
    rw [cons_as_smul, smul_assoc, ih], refl
  end }

lemma prod_eq_self (w : coprod G) : list.prod (w.val.map (λ l, of l.snd.val)) = w :=
begin
  cases w with ls hl, induction ls with p ls ih,
  { refl, }, { cases p, rw [list.map_cons, list.prod_cons, ih hl.tail, cons_as_mul], },
end

end monoids

-- we now do the case of groups.
variables {ι : Type*} {G : Π i : ι, Type*} [Π i, group (G i)]
  [decidable_eq ι] [∀ i, decidable_eq (G i)]

@[simps]
instance coprod_inv : has_inv (coprod G) :=
⟨λ w, ⟨list.reverse (w.val.map $ λ l, ⟨l.fst, l.snd.val⁻¹, inv_ne_one.mpr l.snd.property⟩),
  begin
    rw [list.map_reverse, list.chain'_reverse, list.map_map, function.comp],
    convert w.property, ext, exact ne_comm,
  end⟩⟩

instance : group (coprod G) :=
{ mul_left_inv := begin
    intro w, -- possibly this should all be deduced from some more general result
    conv_lhs { congr, rw ←prod_eq_self w⁻¹, skip, rw ←prod_eq_self w },
    cases w with ls _,
    rw [subtype.val_eq_coe, coprod_inv_inv_coe, list.map_reverse, list.map_map],
    dsimp only,
    induction ls with p ls ih,
    { apply mul_one, },
    rw [list.map_cons, list.reverse_cons, list.prod_append, list.map_cons, list.prod_cons,
      list.prod_nil, mul_one, function.comp_apply, mul_assoc, list.prod_cons,
      ←mul_assoc _ (of p.snd.val), ←of.map_mul, mul_left_inv, of.map_one, one_mul, ih],
  end,
  ..coprod_inv,
  ..coprod_monoid }

#exit
import group_theory.semidirect_product
import group_theory.free_group

open free_group multiplicative semidirect_product

universes u v

def free_group_hom_ext {α G : Type*} [group G] {f g : free_group α →* G}
  (h : ∀ a : α, f (of a) = g (of a)) (w : free_group α) : f w = g w :=
free_group.induction_on w (by simp) h (by simp) (by simp {contextual := tt})

def free_group_equiv {α β : Type*} (h : α ≃ β) : free_group α ≃* free_group β :=
{ to_fun := free_group.map h,
  inv_fun := free_group.map h.symm,
  left_inv := λ w, begin rw [← monoid_hom.comp_apply],
    conv_rhs {rw ← monoid_hom.id_apply (free_group α) w},
     exact free_group_hom_ext (by simp) _ end,
  right_inv := λ w, begin rw [← monoid_hom.comp_apply],
    conv_rhs {rw ← monoid_hom.id_apply (free_group β) w},
     exact free_group_hom_ext (by simp) _ end,
  map_mul' := by simp }

def free_group_perm {α : Type u} : equiv.perm α →* mul_aut (free_group α) :=
{ to_fun := free_group_equiv,
  map_one' := by ext; simp [free_group_equiv],
  map_mul' := by intros; ext; simp [free_group_equiv, ← free_group.map.comp] }

def phi : multiplicative ℤ →* mul_aut (free_group (multiplicative ℤ)) :=
(@free_group_perm (multiplicative ℤ)).comp
  (mul_action.to_perm (multiplicative ℤ) (multiplicative ℤ))

example : free_group bool ≃* free_group (multiplicative ℤ) ⋊[phi] multiplicative ℤ :=
{ to_fun := free_group.lift (λ b, cond b (inl (of (of_add (0 : ℤ)))) (inr (of_add (1 : ℤ)))),
  inv_fun := semidirect_product.lift
    (free_group.lift (λ a, of ff ^ (to_add a) * of tt * of ff ^ (-to_add a)))
    (gpowers_hom _ (of ff))
    begin
      assume g,
      ext,
      apply free_group_hom_ext,
      assume b,
      simp only [mul_equiv.coe_to_monoid_hom,
        gpow_neg, function.comp_app, monoid_hom.coe_comp, gpowers_hom_apply,
        mul_equiv.map_inv, lift.of, mul_equiv.map_mul, mul_aut.conj_apply, phi,
        free_group_perm, free_group_equiv, mul_action.to_perm,
        units.smul_perm_hom, units.smul_perm],
      dsimp [free_group_equiv, units.smul_perm],
      simp [to_units, mul_assoc, gpow_add]
    end,
  left_inv := λ w, begin
    conv_rhs { rw ← monoid_hom.id_apply _ w },
    rw [← monoid_hom.comp_apply],
    apply free_group_hom_ext,
    intro a,
    cases a; refl,
  end,
  right_inv := λ s, begin
    conv_rhs { rw ← monoid_hom.id_apply _ s },
    rw [← monoid_hom.comp_apply],
    refine congr_fun (congr_arg _ _) _,
    apply semidirect_product.hom_ext,
    { ext,
      { simp only [right_inl, mul_aut.apply_inv_self, mul_right,
          mul_one, monoid_hom.map_mul, gpow_neg, lift_inl,
          mul_left, function.comp_app, left_inl, cond, monoid_hom.map_inv,
          monoid_hom.coe_comp, monoid_hom.id_comp, of_add_zero,
          inv_left, lift.of, phi, free_group_perm, free_group_equiv,
          mul_action.to_perm, units.smul_perm_hom, units.smul_perm],
        dsimp [free_group_equiv, units.smul_perm],
        simp,
        simp only [← monoid_hom.map_gpow],
        simp [- monoid_hom.map_gpow],
        rw [← int.of_add_mul, one_mul],
        simp [to_units] },
      { simp } },
    { apply monoid_hom.ext_mint,
      refl }
  end,
  map_mul' := by simp }

#exit

open equiv set nat

variables {S : set ℕ} (π : perm S) (x : S)
set_option trace.simplify.rewrite true
lemma set_S_wf {α : Type*} [group α] (a b c : α) (hab : c * a⁻¹ = c * b⁻¹) : a = b :=
by simp * at *

#print set_S_wf

#exit
import tactic.rcases

universes u

inductive word₀
| blank : word₀
| concat : word₀ → word₀ → word₀

open word₀
infixr ` □ `:80 := concat

@[simp] lemma ne_concat_self_left : ∀ u v, u ≠ u □ v
| blank    v h := word₀.no_confusion h
| (u □ u') v h := ne_concat_self_left u u' (by injection h)

@[simp] lemma ne_concat_self_right : ∀ u v, v ≠ u □ v
| u blank    h := word₀.no_confusion h
| u (v □ v') h := ne_concat_self_right v v' (by injection h)

@[simp] lemma concat_ne_self_right (u v : word₀) : u □ v ≠ v :=
(ne_concat_self_right _ _).symm

@[simp] lemma concat_ne_self_left (u v : word₀) : u □ v ≠ u :=
(ne_concat_self_left _ _).symm

inductive hom₀ : word₀ → word₀ → Sort*
| α_hom : ∀ (u v w : word₀), hom₀ ((u □ v) □ w) (u □ (v □ w))
| α_inv : ∀ (u v w : word₀), hom₀ (u □ (v □ w)) ((u □ v) □ w)
| tensor_id : ∀ {u v} (w), hom₀ u v → hom₀ (u □ w) (v □ w)
| id_tensor : ∀ (u) {v w}, hom₀ v w → hom₀ (u □ v) (u □ w)

inductive hom₀.is_directed : ∀ {v w}, hom₀ v w → Prop
| α : ∀ {u v w}, hom₀.is_directed (hom₀.α_hom u v w)
| tensor_id : ∀ (u) {v w} (s : hom₀ v w), hom₀.is_directed s →
  hom₀.is_directed (hom₀.tensor_id u s)
| id_tensor : ∀ {u v} (w) (s : hom₀ u v), hom₀.is_directed s →
  hom₀.is_directed (hom₀.id_tensor w s)

lemma hom₀.ne {u v} (s : hom₀ u v) : u ≠ v :=
by induction s; simp *

lemma hom₀.subsingleton_aux :
  ∀ {u v u' v'} (hu : u = u') (hv : v = v')
    (s : hom₀ u v) (s' : hom₀ u' v'), s.is_directed →
    s'.is_directed → s == s' :=
begin
  assume u v u' v' hu hv s s' hs hs',
  induction hs generalizing u' v',
  { cases hs',
    { simp only at hu hv,
      rcases hu with ⟨⟨rfl, rfl⟩, rfl⟩,
      refl },
    { simp only at hu hv,
      rcases hu with ⟨rfl, rfl⟩,
      simp * at * },
    { simp only at hu hv,
      rcases hu with ⟨rfl, rfl⟩,
      simp * at * } },
  { cases hs',
    { simp only at hu hv,
      rcases hu with ⟨⟨rfl, rfl⟩, rfl⟩,
      simp * at * },
    { simp only at hu hv,
      rcases hu with ⟨rfl, rfl⟩,
      rcases hv with ⟨rfl, _⟩,
      simp only [heq_iff_eq],
      rw [← heq_iff_eq],
      exact hs_ih rfl rfl _ (by assumption) },
    { simp only at hu hv,
      rcases hu with ⟨rfl, rfl⟩,
      rcases hv with ⟨rfl, rfl⟩,
      exact (hom₀.ne hs'_s rfl).elim } },
  { cases hs',
    { simp only at hu hv,
      rcases hu with ⟨⟨rfl, rfl⟩, rfl⟩,
      simp * at * },
    { simp only at hu hv,
      rcases hu with ⟨rfl, rfl⟩,
      rcases hv with ⟨rfl, rfl⟩,
      exact (hom₀.ne hs'_s rfl).elim },
    { simp only at hu hv,
      rcases hu with ⟨rfl, rfl⟩,
      rcases hv with ⟨_, rfl⟩,
      simp only [heq_iff_eq],
      rw [← heq_iff_eq],
      exact hs_ih rfl rfl _ (by assumption) } }
end

lemma hom₀.subsingleton {u v}
  (s s' : hom₀ u v) (hs : s.is_directed)
  (hs' : s'.is_directed) : s = s' :=
eq_of_heq (hom₀.subsingleton_aux rfl rfl _ _ hs hs')

#exit
import order.conditionally_complete_lattice
import order.lattice_intervals

lemma Z {X : Type} [conditionally_complete_lattice X] [densely_ordered X]
  (a b : X) (h : a < b) : Inf (set.Ioc a b) = a :=
le_antisymm
  begin
    by_contra h1,
    set s := (Inf (set.Ioc a b)) ⊔ a,
    have has : a < s, from lt_iff_le_not_le.2
      ⟨le_sup_right, λ hsa, h1 (le_trans le_sup_left hsa)⟩,
    rcases densely_ordered.dense _ _ has with ⟨c, hac, hcs⟩,
    have hIb : Inf (set.Ioc a b) ≤ b, from cInf_le bdd_below_Ioc (set.mem_Ioc.2 ⟨h, le_refl _⟩),
    have hsb : s ≤ b, from sup_le hIb (le_of_lt h),
    have hIc : Inf (set.Ioc a b) ≤ c, from cInf_le bdd_below_Ioc
      (set.mem_Ioc.2 ⟨hac, le_of_lt (lt_of_lt_of_le hcs hsb)⟩),
    have hsc : s ≤ c, from sup_le hIc (le_of_lt hac),
    exact not_le_of_gt hcs hsc,
  end
  (le_cInf ⟨b, set.mem_Ioc.2 ⟨h, le_refl _⟩⟩
    (λ c hc, le_of_lt (set.mem_Ioc.1 hc).1))
#print Z
#exit
class group (set : Type) :=
(add: set → set → set)

structure group_obj :=
(set : Type)
(group : group set)

instance coe_to_sort : has_coe_to_sort group_obj :=
{ S := Type,
  coe := group_obj.set }

instance group_obj_group (G : group_obj) : group G := G.group

infix `+` := group.add

structure group_morphism (G H : group_obj) :=
(f: G → H)
(additive: ∀ g h : G.set, f(g + h) = (f g) + (f h))


#exit

import algebra.field
import tactic

example {R : Type} [linear_ordered_field R] (d : R) : d * (d + 3) / 2 = (d + 2) * (d + 1) / 2 - 1 :=
begin
  ring,

end

theorem thm (a b : ℤ) : a * (1 + b) - a = a * b :=
(mul_add a 1 b).symm ▸ (mul_one a).symm ▸ add_sub_cancel' a (a * b)

example : ∀ p q : Prop, p ∧ q → q ∧ p :=
λ (p q : Prop) (h : p ∧ q), and.intro (and.right h) (and.left h)

import algebra.ring algebra.group_power
import tactic

example {R : Type} [comm_ring R] (x : R) (hx : x^2 + x + 1 = 0) :
  x^4 = x :=
calc x^4 = x ^ 4 + x * (x ^ 2 + x + 1) : by rw hx; ring
... = x * (x ^ 2 + 1) * (x + 1) : by ring
... = _ : _

lemma lem1 {R : Type} [semiring R] {T : R} (hT : T = T^2 + 1) (n : ℕ) :
  T^n.succ = T^n.succ.succ + T^n :=
calc T ^ n.succ = T ^ n * (T ^ 2 + 1) : by rw [← hT, pow_succ']
... = _ : by simp only [pow_succ', pow_zero, one_mul, mul_assoc, mul_add, mul_one]

lemma lem2 {R : Type} [semiring R] {T : R} (hT : T = T^2 + 1) (k : ℕ) :
  T^(k + 3) + T ^ k + T = T :=
begin
  induction k with k ih,
  { conv_rhs { rw [hT, pow_two], congr, congr, rw hT },
    simp [pow_succ, mul_assoc, add_assoc, add_mul, add_comm, add_left_comm] },
  { calc T ^ (k + 4) + T ^ (k + 1) + T
        = T ^ (k + 4) + T ^ (k + 1) + (T ^ 2 + 1) : by rw [← hT]
    ... = (T ^ (k + 3) + T ^ k + T) * T + 1 :
      by simp only [pow_succ', one_mul, pow_zero, mul_assoc, add_mul, mul_one,
        add_assoc]
    ... = T^2 + 1 : by rw ih; simp only [pow_succ', one_mul, pow_zero, mul_assoc, add_mul, mul_one,
        add_assoc]
    ... = T : hT.symm }
end

lemma lem3 {R : Type} [semiring R] {T : R} (hT : T = T^2 + 1) (n k : ℕ) :
  T^(k + 3) + T ^ k + T ^ (n + 1) = T ^ (n + 1) :=
begin
  induction n with n ih,
  { rw [zero_add, pow_one, lem2 hT] },
  { rw [lem1 hT n.succ, add_comm _ (T ^ n.succ), ← add_assoc, ih] }
end

lemma lem4 {R : Type} [semiring R] {T : R} (hT : T = T^2 + 1) : T^7 = T :=
calc T ^ 7 = T ^ 7 + T ^ 4 + T ^ 1 :
  by conv_lhs { rw [← lem3 hT 6 1] };
    simp only [pow_succ', one_mul, pow_zero, mul_assoc, add_mul, mul_one, add_assoc, add_comm]
... = _ : by rw lem3 hT 0 4; simp

example {R : Type} [comm_ring R] (T : R) (hT : T = T^2 + 1) : T^7 = T :=
calc T ^ 7 = (T ^ 8 + T ^ 7 + (T ^ 6 + T ^ 4) + (T ^ 5 + T ^ 3) + T ^ 2 + 1) : begin
  conv_lhs { rw [lem1 hT 6, lem1 hT 5, lem1 hT 4, lem1 hT 3, lem1 hT 2, lem1 hT 1, lem1 hT 0] },
  ring_exp,
end
... = T^8 + (T ^ 7 + T ^ 5) + T ^ 4 + T ^ 3 + T + 1 : begin
  rw [← lem1 hT 3, ← lem1 hT 4, lem1 hT 1],
  ring_exp,
end
... = (T ^ 8 + T ^ 6) + T ^ 4 + T ^ 3 + T + 1 :
  begin
    rw [← lem1 hT 5],
  end
... = T ^ 7 + T ^ 4 + T ^ 3 + T + 1 :
  begin
    rw [← lem1 hT 6],

  end


example {R : Type} [comm_semiring R] (T : R) (hT : T = T^2 + 1) : T^7 = T :=
calc T^7 = T^6 * T : by ring
... = T^6 * (T^2 + 1) :


example {R : Type} [comm_ring R] (T : R) (hT : T = T^2 + 1) :
  T^7 = T :=
calc T ^ 7 = T * ((T^2 + 1)^2 - T^2) * (T + 1) * (T - 1) + T : by ring
... = 1 : begin
  rw ← hT,  ring

end

example {R : Type} [comm_ring R] (T : R) (hT : T = T^2 + 1) :
  T^7 = T :=
calc T ^ 7 = T * (T^2 + T + 1) * (T^2 - T + 1) * (T + 1) * (T - 1) + T : by ring
... = _ : sorry

example {R : Type} [comm_semiring R] (T : R) (hT : T = T^2 + 1) :
  T^7 = T :=
calc T ^ 7 = T ^ 3 * T ^ 3 : by simp[pow_succ, mul_assoc]
... = (T ^ 2 + 1)^3 * T^3 : by rw ← hT
... = _ : begin
  ring_exp,

end


#exit
import logic.basic

def type_of {α  : Sort*} (a : α) := α

#reduce type_of $ type_of $ type_of @flip
#reduce type_of $ type_of $ @flip (type_of @flip) (type_of @flip) (type_of @flip)
#exit
import data.real.nnreal
import algebra.big_operators
import topology.algebra.infinite_sum
import tactic
import order.lexicographic

open_locale nnreal big_operators

def mask_fun (f : ℕ → ℝ≥0) (mask : ℕ → Prop) [∀ n, decidable (mask n)] : ℕ → ℝ≥0 :=
λ n, if mask n then f n else 0

lemma exists_smul_le_sum {α M : Type*} [linear_ordered_cancel_add_comm_monoid M] (s : finset α)
  (hs : s.nonempty) (f : α → M) : ∃ a ∈ s, finset.card s •ℕ f a ≤ ∑ x in s, f x :=
begin
  classical,
  induction s using finset.induction_on with a s has ih,
  { cases hs with a ha,
    exact ⟨a, by simp *⟩ },
  { simp only [finset.card_insert_of_not_mem has, finset.sum_insert has, succ_nsmul],
    by_cases hs : s.nonempty,
    { rcases ih hs with ⟨b, hbs, hs⟩,
      by_cases f a ≤ f b,
      { use [a, by simp],
        exact add_le_add (le_refl _) (le_trans (nsmul_le_nsmul_of_le_right h _) hs) },
      { use [b, finset.mem_insert_of_mem hbs],
        exact add_le_add (le_of_not_le h) hs } },
    { use a,
      simp [(finset.eq_empty_or_nonempty s).resolve_right hs] } },
end

lemma exists_partition (N : ℕ) (hN : 0 < N) (f : ℕ → ℝ≥0) (hf : ∀ n, f n ≤ 1) :
  ∃ (m : ℕ), f m ≤ (∑' n, f n) / N + 1 :=
begin
  split,
  { rintros ⟨mask, _, h₁, h₂⟩,
    cases h₁ 0 with m hm,
    use m, dsimp at *,
         }
end

#exit
import data.real.nnreal
import algebra.big_operators
import data.list.min_max
import tactic

open_locale nnreal
open_locale big_operators




#exit
instance (n : ℕ) (h : 0 < n) : denumerable (fin n × ℕ) :=
@denumerable.of_encodable_of_infinite _ _
  (infinite.of_injective (λ i : nat, (fin.mk 0 h, i))
    (λ _ _, by simp))



#exit
import tactic

set_option profiler true
example {R : Type} [comm_ring R] (α β γ : R)
  (h : α + β + γ = 0):
  (α - β)^2 * (α - γ)^2 * (β - γ)^2 =
  -4 * (α * β + β * γ + α * γ) ^3- 27 * (α * β * γ)^2 :=
begin
  rw [add_assoc, add_eq_zero_iff_eq_neg] at h,
  subst h,
  ring,
end


#print buffer

def fast_choose (n k : ℕ) : ℕ :=
n.factorial / ((n - k).factorial * k.factorial)

def C : ℕ → buffer ℕ
| 0 := buffer.nil.push_back 1
| 1 := (C 0).push_back 1
| n@(x+1) :=
  let n2 := (n * x) / 2 in
  let C := C x in
  let b : ℕ:= 2^n2 - ((list.fin_range x).map
    (λ m : fin x, have h : m.val < x, from m.2,
      let nx : ℕ := x - m  in
      fast_choose x m * C.read' (m + 1) * 2^
        (((nx - 1) * nx) / 2))).sum in
  C.push_back b

def list_digits_to_string : list ℕ → string :=
λ l, l.foldl (λ s n, repr n ++ s) ""

#eval let n :=9 in (nat.digits (n) ((C n).read' n)).reverse


#exit
import logic.basic
import logic.function.basic

-- term `n` is a function with `n` arguments
inductive term (α : Type) (arity : α → ℕ) : ℕ → Type
| func : Π a, term (arity a)
| var  : ℕ → term 0
| app  : Π {n : ℕ}, term n.succ → term 0 → term n

variables {α : Type} (arity : α → ℕ)

open term

meta def lt [has_lt α] [decidable_rel (@has_lt.lt α _)] :
  Π {n m}, term α arity n → term α arity m → bool
| _ _ (func a) (func b) := a < b
| _ _ (func a) (var _) := ff
| n m (func a) (app _ _) := n < m
| n m (var _) (func _) := if n < m then tt else ff
| _ _ (var i) (var j) := i < j
| _ _ (var i) (app _ _) := tt
| n m (app _ _) (func _) := n < m
| _ _ (app _ _) (var _) := ff
| n m (app f x) (app g y) :=
  cond (lt f g)
    tt
    (cond (lt g f)
      ff
      (lt x y))

instance (n : ℕ) : has_coe_to_fun (term α arity n.succ) :=
{ F   := λ _, term α arity 0 → term α arity n,
  coe := term.app }

def subst (n : ℕ) : term α arity 0 → term α arity 0 →

#exit
import algebra.group

@[derive decidable_eq, derive has_reflect] inductive gterm : Type
| X : ℕ → gterm
| one : gterm
| mul : gterm → gterm → gterm
| inv : gterm → gterm


meta instance : has_repr gterm := ⟨λ g, (`(%%(reflect g) : gterm)).to_string⟩

instance : has_mul gterm := ⟨gterm.mul⟩

instance : has_one gterm := ⟨gterm.one⟩

instance : has_inv gterm := ⟨gterm.inv⟩

open gterm

inductive geq : gterm → gterm → Type
| X : ∀ n, geq (X n) (X n)
| one : geq 1 1
| mul : ∀ {a b c d}, geq a b → geq c d → geq (a * c) (b * d)
| inv : ∀ {a b}, geq a b → geq (a⁻¹) (b⁻¹)
| mul_assoc : ∀ {a b c}, geq (a * b * c) (a * (b * c))
| one_mul : ∀ a, geq (1 * a) a
| inv_mul : ∀ a, geq (a⁻¹ * a) 1
| refl : ∀ (a), geq a a
| symm : ∀ {a b}, geq a b → geq b a
| trans : ∀ {a b c}, geq a b → geq b c → geq a c

meta def to_expr (a b : gterm) (h : geq a b) : expr :=
begin
  induction h,
  { exact expr.app (expr.const `geq.refl []) (reflect h) },
  { exact expr.const `geq.one [] },
  { exact expr.app (expr.app (expr.app (expr.app (expr.app (expr.app (expr.const `geq.mul []) (reflect h_a)) (reflect h_b))
      (reflect h_c)) (reflect h_d)) h_ih_ᾰ) h_ih_ᾰ_1 },
  { exact expr.app (expr.app (expr.app (expr.const `geq.inv []) (reflect h_a)) (reflect h_b)) h_ih },
  { exact expr.app (expr.app (expr.app (expr.const `geq.mul_assoc []) (reflect h_a))
      (reflect h_b)) (reflect h_c) },
  {  exact expr.app (expr.const `geq.one_mul []) (reflect h) },
  { exact expr.app (expr.const `geq.inv_mul []) (reflect h) },
  { exact expr.app (expr.const `geq.refl []) (reflect h) },
  { exact expr.app (expr.app (expr.app (expr.const `geq.symm []) (reflect h_a)) (reflect h_b)) h_ih },
  { exact expr.app (expr.app (expr.app (expr.app (expr.app (expr.const `geq.trans []) (reflect h_a))
      (reflect h_b)) (reflect h_c)) h_ih_ᾰ) h_ih_ᾰ_1 }
end

meta instance (a b : gterm): has_repr (geq a b) :=
⟨λ g, (to_expr _ _ g).to_string⟩

attribute [refl] geq.refl
attribute [symm] geq.symm
attribute [trans] geq.trans


/-- `subst a b t` replaces occurences of `a` in `t` with `b` -/
def subst (a b : gterm) : gterm → gterm
| (mul x y) :=
  if a = x
    then if a = y
      then b * b
      else b * subst y
    else if a = y
      then subst x * b
      else subst x * subst y
| (inv x) :=
  if a = x
    then b⁻¹
    else (subst x)⁻¹
| (X n) := if a = X n then b else X n
| 1 := if a = 1 then b else 1

def geq_subst (a b : gterm) (h : geq a b) :
  ∀ t : gterm, geq t (subst a b t)
| (mul x y) :=
  begin
    dunfold subst,
    split_ifs;
    apply geq.mul;
    try { rw ← h_1 };
    try { rw ← h_2 };
    try { exact h };
    try { exact geq_subst _ }
  end
| (inv x) :=
  begin
    dunfold subst,
    split_ifs;
    apply geq.inv;
    try { rw ← h_1 };
    try { exact h };
    try { exact geq_subst _ }
  end
| (X n) :=
  begin
    dunfold subst,
    split_ifs,
    { rw ← h_1, assumption },
    { refl }
  end
| 1 :=
  begin
    dunfold subst,
    split_ifs,
    { rw ← h_1, assumption },
    { refl }
  end

infixl ` ≡ ` := geq

def geq.mul_inv (x) : geq (x * x⁻¹) 1 :=
calc x * x⁻¹ ≡ 1 * (x * x⁻¹) : (geq.one_mul _).symm
... ≡ ((x * x⁻¹)⁻¹ * (x * x⁻¹)) * (x * x⁻¹) :
  geq.mul (geq.inv_mul _).symm (geq.refl _)
... ≡ (x * x⁻¹)⁻¹ * ((x * x⁻¹) * (x * x⁻¹)) : geq.mul_assoc
... ≡ (x * x⁻¹)⁻¹ * (x * x⁻¹) :
  geq.mul (geq.refl _)
    (calc (x * x⁻¹) * (x * x⁻¹) ≡ x * (x⁻¹ * (x * x⁻¹)) : geq.mul_assoc
      ... ≡ x * x⁻¹ : geq.mul (geq.refl _)
        (geq.mul_assoc.symm.trans ((geq.mul (geq.inv_mul _) (geq.refl _)).trans (geq.one_mul _))))
... ≡ 1 : (geq.inv_mul _)

def geq.mul_one (x : gterm) : x * 1 ≡ x :=
calc x * 1 ≡ x * (x⁻¹ * x) : geq.mul (geq.refl _) (geq.inv_mul _).symm
... ≡ x * x⁻¹ * x : geq.mul_assoc.symm
... ≡ 1 * x : geq.mul (geq.mul_inv _) (geq.refl _)
... ≡ x : (geq.one_mul _)

def find_inv_mul : Π {a b : gterm}, geq a b → list gterm
| _ _ (geq.mul h₁ h₂) := find_inv_mul h₁ ∪ find_inv_mul h₂
| _ _ (geq.inv h) := find_inv_mul h
| _ _ (geq.inv_mul x) := [x]
| _ _ (geq.symm h) := find_inv_mul h
| _ _ (geq.trans h₁ h₂) := find_inv_mul h₁ ∪ find_inv_mul h₂
| _ _ (geq.X _) := []
| _ _ (geq.one) := []
| _ _ (geq.mul_assoc) := []
| _ _ (geq.one_mul _) := []
| _ _ (geq.refl _) := []

#eval find_inv_mul (geq.mul_inv (X 0))

#exit

import data.fin
universes u v
/-- A value which wraps a type. -/
inductive typeinfo (α : Type u) : Type
| of [] : typeinfo

/-- Get the type of the domain of a function type. -/
abbreviation  typeinfo.domain {α : Type u} {β : α → Type v}
  (a : typeinfo (Π (i : α), β i)) : Type u := α

/-- Get the type of the codomain of a function type. -/
abbreviation typeinfo.codomain {α : Type v} {β : Type u}
  (a : typeinfo (α → β)) : Type u := β

/-- Get the type of the codomain of a dependent function type. -/
abbreviation typeinfo.pi_codomain {α : Type v} {β : α → Type u}
  (a : typeinfo (Π (i : α), β i)) : α → Type u := β

variables {M' : Type u}  {ι : Type v}

#check (ι → M')
#check typeinfo (ι → M')
#check typeinfo.of (ι → M')
#check typeinfo.domain (typeinfo.of (ι → M'))

#check (fin 2 → M')
#check typeinfo (fin 2 → M')
#check typeinfo.of (fin 2 → M')
#check typeinfo.domain (typeinfo.of (fin 2 → M') : _)  -- fail, everything else works


#exit

import data.zmod.basic
import data.list

#eval quot.unquot ((finset.univ : finset (fin 4 × fin 4 × fin 4)).filter
  (λ q : fin 4 × fin 4 × fin 4,
    let a := 2 * q.1.val + 1,
        b := 2 * q.2.1.val + 1,
        c := 2 * q.2.2.val in
    ¬ (8 ∣ a + b) ∧
    ¬ (8 ∣ a + b + c) ∧
    ∃ x ∈ [1,4,9,16],∃ y ∈ [1,4,9,16], ∃ z ∈ [1,4,9,16],
     32 ∣ a * x + b * y + c * z)).1


example {X Y Z : Type} (f g : X → Y × Z)
  (h₁ : prod.fst ∘ f = prod.fst ∘ g)
  (h₂ : prod.snd ∘ f = prod.snd ∘ g) :
  f = g :=
calc f = (λ x, ((prod.fst ∘ f) x, (prod.snd ∘ f) x)) : begin
  dsimp,

end
... = _

open nat

attribute [elab_as_eliminator] binary_rec




example {a b c : ℕ+} (h' : ({a, b, c} : finset ℕ+).card = 3) :
  a ≠ b ∧ b ≠ c ∧ c ≠ a :=
begin
  sorry
end

#exit
import data.nat.basic
import tactic

def Delta (f : int → int) := λ x, f (x + 1) - f x

example : Delta ∘ Delta ∘ Delta ∘ Delta  = sorry :=
begin
  funext,
  dsimp [function.comp, Delta],
  abel,

end

#exit
import data.list
import algebra.big_operators

#print finset.sum_

def blah_core {α : Type} (f : α → α) : list α → list α → list (list α)
| l₁ []      := sorry
| l₁ (a::l₂) := l₁ ++ f a :: l₂

def partitions {α : Type} : list α → list (list (list α))
| [] := [[]]
| (a::l) := let P := partitions l in
  P.bind (λ p, ([a] :: p) :: p.bind (λ l, [p.replace]))

def tree_number : Π n : ℕ, array n ℕ
| n :=  let s : list (list ℕ) :=

#exit
import data.list order.pilex

#print list.lex

variables {α : Type*} (r : α → α → Prop) (wf : well_founded r)

def to_pilex : list α → Σ' n : ℕ, fin n → α
| []     := ⟨0, fin.elim0⟩
| (a::l) := ⟨(to_pilex l).fst.succ, fin.cons a (to_pilex l).snd⟩

lemma list.lex_wf : well_founded (list.lex r) :=
subrelation.wf
  _
  (inv_image.wf to_pilex (psigma.lex_wf nat.lt_wf (λ n, pi.lex_wf)))

#exit

#exit
import data.zmod.basic

lemma lemma1 (n : ℕ) {G : Type*} [group G] (a b : G) (h : a * b = b * a) :
  a^n * b = b * a^n :=
begin
  induction n with n ih,
  { rw [pow_zero, one_mul, mul_one] },
  { rw [pow_succ, mul_assoc, ih, ← mul_assoc, h, mul_assoc] }
end

example {G : Type*} [group G] (a b : G) (h : a * b = b * a) : a^2 * b = b * a^2 :=
lemma1 2 a b h


def compute_mod (p : nat.primes) (r : ℤ) : ∀ m : nat, zmod (p ^ m)
| 0 := 1
| 1 := by convert fintype.choose (λ x : zmod p, x^2 = r) sorry; simp
| (n + )



#eval (4⁻¹ : zmod 169)
#eval (-3 + 4 * 13 : int)
#eval (55 ^ 2 : zmod 169)
#eval (127^2 + 4) / 169
#eval (-4 * 95⁻¹ : zmod(13^ 3))
#eval ((95 + 13^2 * 740)^2 : zmod (13^3)) + 4
#eval 13^3

instance : fact (0 < (5 ^ 3)) := sorry

#eval ((finset.univ : finset (zmod (5 ^ 3)))).filter (λ x, x^2 = (-10 : zmod _))


#eval padic_norm 5 (1 / 4 + 156)

open native


meta def x : ℕ → rb_set ℕ × rb_set ℕ
| 0     := (mk_rb_map, mk_rb_map)
| (n+1) := let r := x n in
  let h := r.1.insert (n + 1) in
  let i := r.1.insert n in
  if n % 2 = 0
  then (h, r.2.insert n)
  else (i, r.2.insert n)


meta def y : ℕ → rb_set ℕ
| 0     := mk_rb_map
| (n+1) := (y n).insert n

set_option profiler true

#eval (x 100000).1.contains 0
#eval (y 200000).contains 0

#exit
@[reducible] def V := {s : finset (fin 5) // s.card = 3}

open sum

def edge : V → V → bool
| (inl x) (inl y) := x = y + 1 ∨ y = x + 1
| (inr x) (inr y) := x = y + 2 ∨ y = x + 2
| (inl x) (inr y) := x = y
| (inr x) (inl y) := x = y

@[derive decidable_pred] def is_isom (f : V ≃ V) : Prop :=
∀ x y, edge x y = edge (f x) (f y)

-- #eval fintype.card (V ≃ V)
-- #eval fintype.card {f : V ≃ V // is_isom f}

#exit
import all

open tactic
def foo : nat → Prop
| 0 := true
| (n+1) := (foo n) ∧ (foo n)

meta def mk_foo_expr : nat → expr
| 0 := `(trivial)
| (n+1) :=
  expr.app
    (expr.app
      (reflected.to_expr `(@and.intro (foo n) (foo n)))
      (mk_foo_expr n))
    (mk_foo_expr n)

open tactic

meta def show_foo : tactic unit :=
do `(foo %%nx) ← target,
   n ← eval_expr nat nx,
   exact (mk_foo_expr n)

set_option profiler true

lemma foo_200 : foo 200 :=
by show_foo

#print foo_200

run_cmd do env ← get_env,
  dec ← env.get `foo_200,
  trace (dec.value.fold 0 (fun _ _ n, n + 1) : nat)

lemma X : true :=
by cc
#print level
run_cmd do env ← get_env,
  l ← env.fold (return ([] : list name))
    (λ dec l, do l' ← l,
      let b : bool := expr.occurs
        `((17 : ℕ))
        dec.type,
        return (cond b (dec.to_name :: l') l')),
  trace l.length

#print X

def X : list ℕ → list (ℕ × ℕ)
| []     := []
| (a::l) := X l ++ l.map (prod.mk a)

#eval X [1, 2, 3, 4, 5]

open tactic

#print tactic.set_goals

run_cmd trace_state
#print unify

#exit


import algebra.ring

universe u

variables (X : Type*) [ring X]

-- a contrived example to test recursive and non-recursive constructors
inductive foo : X → X → Prop
| of_mul {a} : foo a (a*a)
| add_two {a b} : foo a b → foo a (b + 2)

inductive foo_eqv : X → X → Prop
| refl (a) : foo_eqv a a
| symm {a b} : foo_eqv a b → foo_eqv b a
| trans {a b c} : foo_eqv a b → foo_eqv b c → foo_eqv a c
| of_mul {a} : foo_eqv a (a*a)
| add_two {a b} : foo_eqv a b → foo_eqv a (b + 2)

variable {α : Type u}
variable (r : α → α → Prop)

inductive eqv_gen' : α → α → Type u
| rel : Π x y, r x y → eqv_gen' x y
| refl : Π x, eqv_gen' x x
| symm : Π x y, eqv_gen' x y → eqv_gen' y x
| trans : Π x y z, eqv_gen' x y → eqv_gen' y z → eqv_gen' x z

def foo_eqv.of_eqv_gen : ∀ {x y}, eqv_gen' (foo X) x y → foo_eqv X x y
| _ _ (eqv_gen'.refl _) := foo_eqv.refl _
| _ _ (eqv_gen'.symm _ _ h) := (foo_eqv.of_eqv_gen h).symm
| _ _ (eqv_gen'.trans a b c hab hbc) := (foo_eqv.of_eqv_gen hab).trans (foo_eqv.of_eqv_gen hbc)
| _ _ (eqv_gen'.rel a b (foo.of_mul)) := foo_eqv.of_mul
| _ _ (eqv_gen'.rel a b (foo.add_two h)) := foo_eqv.add_two (foo_eqv.of_eqv_gen $ eqv_gen'.rel _ _ h)
using_well_founded
{ rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ p, sizeof p.snd.snd)⟩],
  dec_tac := `[simp [measure, inv_image]; apply nat.lt_succ_self _] }

#exit
import tactic.abel

variables {A : Type*} [ring A]

attribute [reducible] id

#eval expr.lex_lt `(id id (1 : nat)) `((2 : nat))

#check `(add_comm_group.to_add_comm_monoid ℤ)

meta def x : expr := `(add_comm_group.to_add_comm_monoid ℤ)
meta def y : expr := `(show add_comm_monoid ℤ, from infer_instance)
#eval (x = y : bool)

def f {A : Type} [add_comm_monoid A] : A → A := id

example (a b c : ℤ) :
  @f ℤ (by tactic.exact y) a + b = b + @f ℤ (by tactic.exact x) a :=
begin
  abel,
end


#exit
open complex
open_locale real

example : (1 : ℂ) ^ (- I * log 2 / (2 * π)) = 2 :=
begin
  rw one_cpow,

end

#exit
import tactic data.nat.basic
import data.nat.prime
import data.fintype

open tactic

#print list.take



meta def test : tactic unit :=
do t ← target,
(lhs, rhs) ← expr.is_eq t,
s ← mk_simp_set tt [] [simp_arg_type.expr ``(mul_one)],
(e₁, e₂) ← tactic.simplify s.1 [] lhs,
tactic.exact e₂

run_cmd do n ← mk_fresh_name, trace n

-- example : 2021 = 5 + nat.choose (4 ^ 3) (nat.choose 2 1) :=
-- begin
--   rw [nat.choose_eq_factorial_div_factorial, nat.choose_eq_factorial_div_factorial];
--   norm_num,
-- end

#exit
import order.order_iso_nat
import order.preorder_hom

namespace partial_order

variables (α : Type*)

/-- For partial orders, one of the many equivalent forms of well-foundedness is the following
flavour of "ascending chain condition". -/
class satisfies_acc [preorder α] : Prop :=
(acc : ∀ (a : ℕ →ₘ α), ∃ n, ∀ m, n ≤ m → a n = a m)

run_cmd tactic.mk_iff_of_inductive_prop ``satisfies_acc `partial_order.satisfies_acc_iff

variables [partial_order α]

lemma wf_iff_satisfies_acc :
  well_founded ((>) : α → α → Prop) ↔ satisfies_acc α :=
begin
  rw [rel_embedding.well_founded_iff_no_descending_seq,
    satisfies_acc_iff, not_nonempty_iff_imp_false],

end

#print native.float



#eval native.float.exp native.float.pi - 23.1407 + 3.8147 * 0.000001
#eval native.float.exp 1

def thing (a b : nat) : nat :=
(a + b).choose a

#exit
import analysis.special_functions.trigonometric

universes u v

#check (Type u -> Type v : Type (max u v + 1)
open real

noncomputable theory

#print real.arcsin

lemma cosh_def (x : ℝ) : cosh x = (exp x + exp (-x)) / 2 :=
by simp only [cosh, complex.cosh, complex.div_re, complex.exp_of_real_re, complex.one_re,
  bit0_zero, add_zero, complex.add_re, euclidean_domain.zero_div, complex.bit0_re,
  complex.one_im, complex.bit0_im, mul_zero, ← complex.of_real_neg, complex.norm_sq];
  ring

lemma sinh_def (x : ℝ) : sinh x = (exp x - exp (-x)) / 2 :=
by simp only [sinh, complex.sinh, complex.div_re, complex.exp_of_real_re, complex.one_re,
  bit0_zero, add_zero, complex.sub_re, euclidean_domain.zero_div, complex.bit0_re,
  complex.one_im, complex.bit0_im, mul_zero, ← complex.of_real_neg, complex.norm_sq];
  ring

lemma cosh_pos (x : ℝ) : 0 < real.cosh x :=
(cosh_def x).symm ▸ half_pos (add_pos (exp_pos x) (exp_pos (-x)))

lemma sinh_strict_mono : strict_mono sinh :=
strict_mono_of_deriv_pos differentiable_sinh (by rw [real.deriv_sinh]; exact cosh_pos)

lemma sinh_arcsinh (x : ℝ) : sinh (arcsinh x) = x :=
have h₂ : 0 ≤ x^2 + 1, from add_nonneg (pow_two_nonneg _) zero_le_one,
have h₁ : 0 < x + sqrt (x^2 + 1),
  from suffices - x < sqrt (x^2 + 1), by linarith,
    lt_of_pow_lt_pow 2 (sqrt_nonneg _)
      begin
        rw [sqr_sqrt h₂, pow_two, pow_two, neg_mul_neg],
        exact lt_add_one _
      end,
begin
  rw [sinh_def, arcsinh, exp_neg, exp_log h₁],
  field_simp [ne_of_gt h₁],
  rw [add_mul, mul_add, mul_add, ← pow_two (sqrt _), sqr_sqrt h₂],
  gen''eralize hy : sqrt (x^2 + 1) = y,
  rw [← sub_eq_zero],
  ring
end

lemma arcsinh_sinh (x : ℝ) : arcsinh (sinh x) = x :=
function.right_inverse_of_injective_of_left_inverse
  sinh_strict_mono.injective sinh_arcsinh _


#exit
import group_theory.sylow

open_locale classical
/-
theorem has_fixed_point {G : Type} [group G] [fintype G] (hG65 : fintype.card G = 65)
  {M : Type} [fintype M] (hM27 : fintype.card M = 27) [mul_action G M] :
  ∃ m : M, ∀ g : G, g • m = m :=
have horbit : ∀
-- begin
--   rcases @incidence.I₃ _ _ incident_with _ with ⟨A, B, C, hAB, hBC, hAC, hABC⟩,

--   have : P ≠ B ∧ P ≠ C ∨ P ≠ A ∧ P ≠ C ∨ P ≠ A ∧ P ≠ B, { finish },
--   wlog hP : P ≠ B ∧ P ≠ C := this using [B C, A C, A B],
--   {  }

-- end


end

#exit

theorem fib_fast_correct : ∀ n, fib_fast n = fib n :=

#exit
import data.equiv.denumerable
open function

structure iso (A : Type) (B : Type) :=
  (a_to_b : A → B)
  (b_to_a : B → A)
  (a_b_a : ∀ a, b_to_a (a_to_b a) = a)
  (b_a_b : ∀ b, a_to_b (b_to_a b) = b)

inductive nat_plus_1 : Type
| null : nat_plus_1
| is_nat (n : ℕ) : nat_plus_1

inductive nat_plus_nat : Type
| left (n : ℕ) : nat_plus_nat
| right (n : ℕ) : nat_plus_nat


-- Task 0
-- Find a bijection between bool and bit. (provided for you as an example)


inductive bit : Type
  | b0 : bit
  | b1 : bit

open bit

def bool_to_bit : bool → bit
| tt := b1
| ff := b0

def bit_to_bool : bit → bool
| b0 := ff
| b1 := tt

def bool_iso_bit : iso bool bit :=
{
  a_to_b := bool_to_bit,
  b_to_a := bit_to_bool,
  a_b_a := λ a, bool.cases_on a rfl rfl,
  b_a_b := λ b, bit.cases_on b rfl rfl,
}

-- Task 1
-- General properties of iso

-- Task 1-1 : Prove that any set has the same cardinality as itself
def iso_rfl {A : Type} : iso A A := ⟨id, id, eq.refl, eq.refl⟩

-- Task 1-2 : Prove that iso is symmetric
def iso_symm {A B : Type} (i : iso A B) : iso B A :=
⟨i.2, i.1, i.4, i.3⟩

-- Task 1-3 : Prove that iso is transitive
def iso_trans {A B C : Type} (ab : iso A B) (bc : iso B C) : iso A C :=
⟨bc.1 ∘ ab.1, ab.2 ∘ bc.2, λ _, by simp [function.comp, bc.3, ab.3],
  by simp [function.comp, bc.4, ab.4]⟩

-- Task 1-4 : Prove the following statement:
-- Given two functions A->B and B->A, if A->B->A is satisfied and B->A is injective, A <=> B
def bijection_alt {A B : Type} (ab : A → B) (ba : B → A)
  (h : ∀ a, ba (ab a) = a) (hba: injective ba) : iso A B :=
⟨ab, ba, h, λ b, hba $ by rw h⟩

-- Task 2
-- iso relations between nat and various supersets of nat

-- nat_plus_1 : a set having one more element than nat. (provided in preloaded)




open nat_plus_1

def nat_iso_nat_plus_1 : iso ℕ nat_plus_1 :=
⟨fun n, nat.cases_on n null is_nat,
  fun n, nat_plus_1.cases_on n 0 nat.succ,
  λ n, by cases n; refl,
  fun n, by cases n; refl⟩

-- nat_plus_nat : a set having size(nat) more elements than nat. (provided in preloaded)


open nat_plus_nat

instance : denumerable nat_plus_nat :=
denumerable.of_equiv (ℕ ⊕ ℕ)
  ⟨λ n, nat_plus_nat.cases_on n sum.inl sum.inr,
   fun n, sum.cases_on n left right,
   fun n, by cases n; refl,
   fun n, by cases n; refl⟩

def nat_iso_nat_plus_nat : iso ℕ nat_plus_nat :=
let e := denumerable.equiv₂ ℕ nat_plus_nat in
⟨e.1, e.2, e.3, e.4⟩


#exit
import data.finset

open finset

variable {α : Type*}

lemma list.take_sublist : ∀ (n : ℕ) (l : list α), l.take n <+ l
| 0     l      := list.nil_sublist _
| (n+1) []     := list.nil_sublist _
| (n+1) (a::l) := list.cons_sublist_cons _ (list.take_sublist _ _)

lemma list.take_subset (n : ℕ) (l : list α) : l.take n ⊆ l :=
list.subset_of_sublist (list.take_sublist _ _)

#print list.mem_diff_iff_of_nop

lemma exists_intermediate_set {A B : finset α} (i : ℕ)
  (h₁ : i + card B ≤ card A) (h₂ : B ⊆ A) :
  ∃ (C : finset α), B ⊆ C ∧ C ⊆ A ∧ card C = i + card B :=
begin
  cases A with A hA, cases B with B hB,
  induction A using quotient.induction_on with A,
  induction B using quotient.induction_on with B,
  classical,
  refine ⟨⟨⟦((B.diff A).take i) ++ A⟧,
    list.nodup_append.2 ⟨list.nodup_of_sublist (list.take_sublist _ _)
      (list.nodup_diff hB), hA, list.disjoint_left.2 (λ a ha h, _)⟩⟩, _⟩,
  have := list.take_subset _ _ ha,  finish [list.mem_diff_iff_of_nodup hB],
  dsimp, simp [finset.subset_iff],



end


#exit
import data.rat.order data.equiv.denumerable data.rat.denumerable

structure rat_iso_rat_without_zero : Type :=
(to_fun : ℚ → ℚ)
(map_ne_zero : ∀ x, to_fun x ≠ 0)
(exists_map_of_ne_zero : ∀ y ≠ 0, ∃ x, to_fun x = y)
(injective : ∀ x y, to_fun x = to_fun y → x = y)
(map_le_map : ∀ x y, x ≤ y → to_fun x ≤ to_fun y)

def denumerable_rat : ℕ → ℕ × list ℚ
| 0     := ⟨1, [0]⟩
| (n+1) :=
let ⟨i, l⟩ := denumerable_rat n in
have h : ∃ m : ℕ, let p := denumerable.equiv₂ ℕ (ℤ × ℕ+) (m + i) in
    nat.coprime p.1.nat_abs p.2,
      from sorry,
let m := nat.find h in
let p := denumerable.equiv₂ ℕ (ℤ × ℕ+) (m + i) in
⟨m + i + 1, ⟨p.1, p.2, p.2.2, nat.find_spec h⟩ :: l⟩

def denumerable_rat' : ℕ → list ℚ
| 0     := []
| (n+1) :=
let p := denumerable.equiv₂ ℕ (ℤ × ℕ+) n in
if h : p.1.nat_abs.coprime p.2.1
then ⟨p.1, p.2.1, p.2.2, h⟩ :: denumerable_rat' n
else denumerable_rat' n

#eval denumerable_rat' 10000

def blah : ℕ → list {x : ℚ // x ≠ 0} × list {x : ℚ // x ≠ 0}
| 0 := ⟨[], [⟨-1, dec_trivial⟩]⟩
| (n+1) :=
let ⟨i, lq, ln, lq0⟩ := blah n in
have h : ∃ m : ℕ, let p := denumerable.equiv₂ ℕ (ℤ × ℕ+) (m + i) in
    nat.coprime p.1.nat_abs p.2,
      from sorry,
let m := nat.find h in
let p := denumerable.equiv₂ ℕ (ℤ × ℕ+) (m + i) in
⟨m + i + 1, ⟨p.1, p.2, p.2.2, nat.find_spec h⟩ :: lq,
  _, _⟩


-- set_option profiler true

-- #eval ((denumerable_rat 100)).2
-- #eval (((list.range 100).map (denumerable.equiv₂ ℕ ℚ))).reverse

-- -- instance denumerable_rat_without_zero :
-- --   denumerable {x : ℚ // x ≠ 0} :=


-- #eval denumerable.equiv₂ ℚ ℕ 0

-- def inbetween (a b : {x : ℚ // x ≠ 0}) : {x : ℚ // x ≠ 0} :=
-- if h : (a : ℚ) + b = 0
-- then ⟨((2 : ℚ) * a + b)/ 3,
--   div_ne_zero (by rw [two_mul, add_assoc, h, add_zero]; exact a.2) (by norm_num)⟩
-- else ⟨(a + b) / 2, div_ne_zero h (by norm_num)⟩

-- attribute [priority 10000] denumerable_rat_without_zero

-- def rat_iso_rat_without_zero_aux : ℕ → list {x : ℚ // x ≠ 0}
-- | 0     := [denumerable.equiv₂ ℕ {x : ℚ // x ≠ 0} 0]
-- | (n+1) :=
-- let q := denumerable.equiv₂ ℕ ℚ (n+1) in
-- let l := rat_iso_rat_without_zero_aux n in
-- option.cases_on (l.filter (λ x : {x : ℚ // x ≠ 0}, x.1 ≤ q)).maximum
--   (option.cases_on (l.filter (λ x : {x : ℚ // x ≠ 0}, q ≤ x.1)).minimum
--     [] (λ x, _))
--   _



theorem nonempty_rat_iso_rat_without_zero :
  nonempty rat_iso_rat_without_zero :=


open nat

def fsum : (ℕ → ℕ) → ℕ → ℕ :=
  λ f n, nat.rec_on n (f 0) (λ n' ihn', f (nat.succ n') + ihn')

open nat

theorem fsum_zero (f) : fsum f 0 = f 0 := rfl
theorem fsum_succ (n f) : fsum f (succ n) = f (succ n) + fsum f n := rfl

def sq : ℕ → ℕ := λ n, n ^ 2
def cb : ℕ → ℕ := λ n, n ^ 3

lemma fsum_id_eq (n) : 2 * fsum id n = n * (n + 1) :=
begin
  induction n with n ih,
  { refl },
  { rw [fsum_succ, mul_add, ih, succ_eq_add_one, id.def],
    ring }
end

lemma fsum_cb_eq (n) : 4 * fsum cb n = (n * (n + 1)) * (n * (n + 1)) :=
begin
  induction n with n ih,
  { refl },
  { rw [fsum_succ, mul_add, ih, succ_eq_add_one, cb],
    simp [mul_add, add_mul, nat.pow_succ, bit0, bit1, mul_assoc,
      mul_comm, mul_left_comm, add_comm, add_assoc, add_left_comm] }
end

theorem nicomachus (n) : sq (fsum id n) = fsum cb n :=
(nat.mul_left_inj (show 0 < 4, from dec_trivial)).1
  (calc 4 * sq (fsum id n) = (2 * fsum id n) * (2 * fsum id n) :
    by simp only [sq, ← nat.pow_eq_pow]; ring
  ... = (n * (n + 1)) * (n * (n + 1)) : by rw [fsum_id_eq]
  ... = _ : by rw [fsum_cb_eq])

#exit

lemma pow_sqr_aux_succ (gas b e : ℕ) :
  pow_sqr_aux (succ gas) b e =
    prod.cases_on (bodd_div2 e)
    (λ r e', bool.cases_on r
      (pow_sqr_aux gas (b * b) e')
      (b * pow_sqr_aux gas (b * b) e')) := rfl

def pow_sqr (b e : ℕ) : ℕ := pow_sqr_aux e b e

lemma bodd_eq_ff : ∀ n, bodd n = ff ↔ even n
| 0 := by simp
| (n+1) := by rw [bodd_succ, even_add, ← bodd_eq_ff]; simp

lemma pow_eq_aux (gas b e : ℕ) (h : e ≤ gas) : pow_sqr_aux gas b e = b ^ e :=
begin
  induction gas with gas ih generalizing e b,
  { rw [nat.eq_zero_of_le_zero h], refl },
  { rw [pow_sqr_aux_succ],
    cases e with e,
    { dsimp [bodd_div2],
      rw [ih _ _ (nat.zero_le _), nat.pow_zero] },
    { rw [bodd_div2_eq],
      have : div2 (succ e) < succ gas,
        from lt_of_lt_of_le
          (by rw [div2_val]; exact nat.div_lt_self (nat.succ_pos _) dec_trivial)
          h,
      rcases hb : bodd (succ e) with tt | ff,
      { dsimp,
        have heven : even (succ e), by rwa bodd_eq_ff at hb,
        rw [ih _ _ (nat.le_of_lt_succ this), div2_val, ← nat.pow_two,
          ← nat.pow_mul, nat.mul_div_cancel' heven] },
      { dsimp,
        have hodd : succ e % 2 = 1, { rw [← not_even_iff, ← bodd_eq_ff, hb], simp },
        rw [ih _ _ (nat.le_of_lt_succ this), div2_val, ← nat.pow_two,
          ← nat.pow_mul, mul_comm, ← nat.pow_succ, nat.succ_eq_add_one,
          add_comm],
        suffices : b ^ (succ e % 2 + 2 * (succ e / 2)) = b ^ succ e, rwa hodd at this,
        rw [nat.mod_add_div] } } }
end

theorem pow_eq (b e : ℕ) : pow_sqr b e = b ^ e :=
pow_eq_aux _ _ _ (le_refl _)

#exit
import data.fintype.basic

open finset
lemma mul_comm_of_card_eq_four (G : Type u) [fintype G] [group G]
  (hG4 : fintype.card G = 4) (g h : G) : G, g * h = h * g :=
example {G : Type*} [fintype G] [group G] (h4 : fintype.card G ≤ 4) :
  ∀ x y : G, x * y = y * x :=
λ g h, classical.by_contradiction $ λ H, begin
  have hn : multiset.nodup [x * y, y * x, x, y, 1],
  { finish [mul_right_eq_self, mul_left_eq_self, mul_eq_one_iff_eq_inv] },
  exact absurd (le_trans (card_le_of_subset (subset_univ ⟨_, hn⟩)) hG4) dec_trivial
end

#exit
import topology.metric_space.closeds
open nat

def strong_rec_on_aux {P : ℕ → Sort*}
  (h : Π n : ℕ, (Π m < n, P m) → P n) :
  Π n m, m < n → P m :=
λ n, nat.rec_on n (λ m h₁, absurd h₁ (not_lt_zero _))
  (λ n ih m h₁, or.by_cases (lt_or_eq_of_le (le_of_lt_succ h₁))
    (ih _)
    (λ h₁, by subst m; exact h _ ih))

lemma strong_rec_on_aux_succ {P : ℕ → Sort*}
  (h : Π n : ℕ, (Π m < n, P m) → P n) (n m h₁):
strong_rec_on_aux h (succ n) m h₁ =
  or.by_cases (lt_or_eq_of_le (le_of_lt_succ h₁))
    (λ hmn, strong_rec_on_aux h _ _ hmn)
    (λ h₁, by subst m; exact h _ (strong_rec_on_aux h _)) := rfl

theorem nat.strong_rec_on_beta_aux {P : ℕ → Sort*} {h} {n : ℕ} :
  (nat.strong_rec_on n h : P n) =
  (strong_rec_on_aux h (succ n) n (lt_succ_self _)) := rfl

theorem nat.strong_rec_on_beta {P : ℕ → Sort*} {h} {n : ℕ} :
  (nat.strong_rec_on n h : P n) =
    h n (λ m hmn, (nat.strong_rec_on m h : P m)) :=
begin
  simp only [nat.strong_rec_on_beta_aux,
    strong_rec_on_aux_succ, or.by_cases, dif_pos, not_lt, dif_neg],
  congr, funext m h₁,
  induction n with n ih,
  { exact (not_lt_zero _ h₁).elim },
  { cases (lt_or_eq_of_le (le_of_lt_succ h₁)) with hmn hmn,
    { simp [← ih hmn, strong_rec_on_aux_succ, or.by_cases, hmn] },
    { subst m, simp [strong_rec_on_aux_succ, or.by_cases] } }
end

def strong_rec' {P : ℕ → Sort*} (h : ∀ n, (∀ m, m < n → P m) → P n) : ∀ (n : ℕ), P n
| n := h n (λ m hm, strong_rec' m)

set_option profiler true

#reduce strong_rec'
  (λ n, show (∀ m, m < n → ℕ) → ℕ, from nat.cases_on n 0 (λ n h, h 0 (succ_pos _)))
  500

#reduce nat.strong_rec_on
  500
  (λ n, show (∀ m, m < n → ℕ) → ℕ, from nat.cases_on n 0 (λ n h, h 0 (succ_pos _)))

#eval strong_rec'
  (λ n, show (∀ m, m < n → ℕ) → ℕ, from nat.cases_on n 0 (λ n h, h 0 (succ_pos _)))
  10000000

#eval nat.strong_rec_on
  10000000
  (λ n, show (∀ m, m < n → ℕ) → ℕ, from nat.cases_on n 0 (λ n h, h 0 (succ_pos _)))
#exit
constant layout : Type → Type
--constant edge_sequence : Type → Type

--inductive T : Π {b : bool}, cond b (layout G) (Σ L : layout G, )

mutual inductive edge_sequence, add_edge_sequence
with edge_sequence : layout G → Type
| single {L : layout G} {e : G.edges} (h : e ∈ L.remaining_edges) : edge_sequence L
| cons {L : layout G} (S : edge_sequence L) {e : G.edges}
  (h : e ∈ (add_edge_sequence S).1.remaining_edges) : edge_sequence L
with add_edge_sequence : Π {L : layout G}, edge_sequence L → layout G × finset G.boxes
| L (single h) := L.add_edge h
| L (cons S h) := let ⟨L', B⟩ := L.add_edge_sequence S in let ⟨L'', B'⟩ := L.1.add_edge h in ⟨L'', B ∪ B'⟩



import topology.basic topology.metric_space.closeds
#print closeds
lemma closure_inter_subset_inter_closure' {X Y : set ℝ} :
  closure (X ∩ Y) ⊆ closure X ∩ closure Y :=
galois_connection.u_inf
  begin show galois_connection (closure : set ℝ → closeds ℝ) (subtype.val),  end

#exit
import data.fintype.basic
open finset

set_option class.instance_max_depth 1000

#eval (((univ : finset (vector (fin 10) 3)).filter
  (λ v : vector (fin 10) 3, (v.nth 0 = 6 ∨ v.nth 1 = 8 ∨ v.nth 2 = 2)
    ∧ (7 : fin 10) ∉ v.1 ∧ (3 : fin 10) ∉ v.1 ∧ (8 : fin 10) ∉ v.1
    ∧ ((v.nth 1 = 6 ∨ v.nth 2 = 6) ∨ (v.nth 0 = 1 ∨ v.nth 2 = 1) ∨
      (v.nth 0 = 4 ∨ v.nth 1 = 4))
    ∧ ((v.nth 1 = 7 ∨ v.nth 2 = 7) ∨ (v.nth 0 = 8 ∨ v.nth 2 = 8) ∨
      (v.nth 0 = 0 ∨ v.nth 1 = 0))
    )).map
  ⟨vector.to_list, subtype.val_injective⟩)

universes u v

def map_copy_aux {α : Type u} {β : Type v} {n m : ℕ} (f : α → β) :
  ℕ → array n α → array m β → array m β
| r x y := if h : r < n ∧ r < m then
             let fn : fin n := ⟨r, and.elim_left h⟩ in
             let fm : fin m := ⟨r, and.elim_right h⟩ in
             have wf : m - (r + 1) < m - r,
               from nat.lt_of_succ_le $ by rw [← nat.succ_sub h.2, nat.succ_sub_succ],
             map_copy_aux (r + 1) x $ y.write fm (f $ x.read fn)
           else y
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ a, m - a.1)⟩]}

#exit
import data.zmod.basic

#eval fintype.choose _
  (show ∃! f : zmod 4 → zmod 4, ∀ x y, f (x * y) = f x * f y
    ∧ ∀ x, f x = 1 ↔ x = 1 ∧ f ≠ id, from sorry) 3


example (n : ℕ) (hn : n ≤ 4) : false :=
begin
  classical,
  interval_cases n,
  repeat {sorry}
end

theorem zagier (R : Type) [comm_ring R]
  [fintype (units R)] : card (units R) ≠ 5 :=
if h : (-1 : R) = 1
then _
else _


#exit
import data.finset
#print no_zero_divisors
open nat
lemma mul_add (t a b : nat) : t * (a + b) = t * a + t * b :=

begin

  induction b with B hB,

  -- b base case
  rw add_zero a,
  rw mul_zero t,
  rw add_zero (t*a),
  refl,

  -- joint inductive step
  rw add_succ a B,
  rw mul_succ t (a + B),
  rw hB,
  rw add_assoc (t*a) (t*B) t,
  rw <- mul_succ t B,

end

#exit
import data.finset
import tactic

/-!
Test
-/
#print auto.split_hyps
open_locale classical
namespace tactic.interactive

meta def split_hyps := auto.split_hyps

end tactic.interactive



lemma Z (X : Type*) (a b c d e f : X) (h : ({a,b,c} : set X) = {d,e,f}) :
  a = d ∧ b = e ∧ c = f ∨ a = d ∧ b = f ∧ c = e ∨ a = e ∧ b = d ∧ c = f
  ∨ a = e ∧ b = f ∧ c = d ∨ a = f ∧ b = d ∧ c = e ∨ a = f ∧ b = e ∧ c = d :=
begin sorry
  -- simp [set.ext_iff] at h,
  -- have := h a, have := h b, have := h c, have := h d, have := h e, have := h f,
  -- by_cases a = d; by_cases a = e; by_cases a = f;
  -- by_cases b = d; by_cases b = e; by_cases b = f;
  -- by_cases c = d; by_cases c = e; by_cases c = f;
  -- simp [*, eq_comm] at *; simp * at *; simp * at *,
  -- finish using [h a, h b, h c, h d, h e, h f]


end

example : false :=
begin
  have := Z ℕ 0 1 1 0 0 1,
  simpa using this,

end

example (X : Type*) (a b c d : X) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) ↔
  ∀ x : X, (x = a ∨ x = b) ↔ (x = c ∨ x = d) :=
⟨λ h x, by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; simp [or_comm],
  λ h, begin
    have := h a, have := h b, have := h c, have := h d,
    by_cases a = c; by_cases a = d;
    simp [*, eq_comm] at *; simp * at *; simp * at *
  end⟩
#exit
import data.finset

lemma X (X : Type) [decidable_eq X] (x y : X) : ({x, y} : finset X) = {y, x} :=
begin
  simp [finset.ext, or_comm]

end

lemma Y (X : Type) [decidable_eq X] (x y : X) : ({x, y} : finset X) = {y, x} :=
begin
  finish [finset.ext],

end

#print X
#print Y

#exit

import all


def fact (n : ℕ) : ℕ :=
let f : ℕ → ℕ := λ n, nat.rec_on n 1 (λ n fact, (n + 1) * fact) in
f n

def fact' (n : ℕ) : ℕ :=
let f : ℕ → ℕ := λ n, well_founded.fix nat.lt_wf
  (λ n fact, show ℕ, from nat.cases_on n (λ _, 1)
    (λ n fact, (n + 1) * fact n n.lt_succ_self) fact)
  n in
f n

#eval fact' 5

#exit
import data.fintype.basic algebra.big_operators

open finset

open_locale classical

lemma prod_add {α R : Type*} [comm_semiring R] (f g : α → R) (s : finset α) :
  s.prod (λ a, f a + g a) =
  s.powerset.sum (λ t : finset α, t.prod f * (s.filter (∉ t)).prod g) :=
calc s.prod (λ a, f a + g a)
    = s.prod (λ a, ({false, true} : finset Prop).sum
      (λ p : Prop, if p then f a else g a)) : by simp
... = (s.pi (λ _, {false, true})).sum (λ p : Π a ∈ s, Prop,
      s.attach.prod (λ a : {a // a ∈ s}, if p a.1 a.2 then f a.1 else g a.1)) : prod_sum
... = s.powerset.sum (λ (t : finset α), t.prod f * (s.filter (∉ t)).prod g) : begin
  refine eq.symm (sum_bij (λ t _ a _, a ∈ t) _ _ _ _),
  { simp [subset_iff]; tauto },
  { intros t ht,
    erw [prod_ite (λ a : {a // a ∈ s}, f a.1) (λ a : {a // a ∈ s}, g a.1) (λ x, x)],
    refine congr_arg2 _
      (prod_bij (λ (a : α) (ha : a ∈ t), ⟨a, mem_powerset.1 ht ha⟩)
         _ _ _
        (λ b hb, ⟨b, by cases b; finish⟩))
      (prod_bij (λ (a : α) (ha : a ∈ s.filter (∉ t)), ⟨a, by simp * at *⟩)
        _ _ _
        (λ b hb, ⟨b, by cases b; finish⟩));
    intros; simp * at *; simp * at * },
  { finish [function.funext_iff, finset.ext, subset_iff] },
  { assume f hf,
    exact ⟨s.filter (λ a : α, ∃ h : a ∈ s, f a h),
      by simp, by funext; intros; simp *⟩ }
end

lemma card_sub_card {α : Type*} {s t : finset α} (hst : t ⊆ s) :
  card s - card t = (s.filter (∉ t)).card :=
begin
  rw [nat.sub_eq_iff_eq_add (card_le_of_subset hst), ← card_disjoint_union],
  exact congr_arg card (finset.ext.2 $ λ _, by split; finish [subset_iff]),
  finish [disjoint_left]
end

lemma sum_pow_mul_eq_add_pow
  {α R : Type*} [comm_semiring R] (a b : R) (s : finset α) :
  s.powerset.sum (λ t : finset α, a ^ t.card * b ^ (s.card - t.card)) =
  (a + b) ^ s.card :=
begin
  rw [← prod_const, prod_add],
  refine finset.sum_congr rfl (λ t ht, _),
  rw [prod_const, prod_const, card_sub_card (mem_powerset.1 ht)]
end




#exit
import topology.metric_space.basic

noncomputable theory

variables {X : Type*} [metric_space X]
variables {Y : Type*} [metric_space Y]
#reduce 200 - 10
/- The metric of any two elements of a metric space is non-negative -/
theorem metric_nonneg : ∀ x y : X, 0 ≤ dist x y := λ x y,
begin
    suffices : 0 ≤ dist y x + dist x y - dist y y,
        rw [dist_self, dist_comm, sub_zero] at this,
        linarith,
    linarith [dist_triangle y x y]
end

/- The product of two metric spaces is also a metric space -/
instance : metric_space (X × Y) :=
{   dist := λ ⟨x₀, y₀⟩ ⟨x₁, y₁⟩, dist x₀ x₁ + dist y₀ y₁,
    dist_self := λ ⟨x, y⟩, show dist x x + dist y y = 0, by simp,
    eq_of_dist_eq_zero := -- Why can't I use λ ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ here?
        λ ⟨x₀, y₀⟩ ⟨x₁, y₁⟩, begin
            --rintros ⟨x₀, y₀⟩ ⟨x₁, y₁⟩,
            -- show dist x₀ x₁ + dist y₀ y₁ = 0 → (x₀, y₀) = (x₁, y₁), intro h,
            -- suffices : dist x₀ x₁ = 0 ∧ dist y₀ y₁ = 0,
            --     rwa [eq_of_dist_eq_zero this.left, eq_of_dist_eq_zero this.right],
            -- split,
            -- all_goals {linarith [metric_nonneg x₀ x₁, metric_nonneg y₀ y₁, h]}
        end,
    dist_comm := λ ⟨x₀, y₀⟩ ⟨x₁, y₁⟩,
        show dist x₀ x₁ + dist y₀ y₁ = dist x₁ x₀ + dist y₁ y₀, by simp [dist_comm],
    dist_triangle := λ ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ ⟨x₂, y₂⟩,
        show dist x₀ x₂ + dist y₀ y₂ ≤ dist x₀ x₁ + dist y₀ y₁ + (dist x₁ x₂ + dist y₁ y₂),
        by linarith

#exit
def definitely_not_false : bool := tt

attribute [irreducible] definitely_not_false

example (f : bool → bool) (h : f definitely_not_false = ff) : f tt = ff := by rw h
example (h : definitely_not_false = ff) : tt = ff := by rw h

attribute [semireducible] definitely_not_false

example (f : bool → bool) (h : f definitely_not_false = ff) : f tt = ff := by rw h
example (h : definitely_not_false = ff) : tt = ff := by rw h

attribute [reducible] definitely_not_false

example (f : bool → bool) (h : f definitely_not_false = ff) : f tt = ff := by rw h -- only one that works
example (h : definitely_not_false = ff) : tt = ff := by rw h


#exit
import data.fintype

#print classical.dec_eq

#print subtype.decidable_eq

#exit
import logic.basic

def X : Type := empty → ℕ

lemma hx : X = (empty → X) :=
calc X = Π i : empty, (λ h : empty, ℕ) i : rfl
... = Π i : empty, (λ h : empty, X) i :
  have (λ h : empty, ℕ) = (λ h : empty, X),
    from funext empty.elim,
  this ▸ rfl

example : X = ℕ :=
begin
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,
  rw hx,


end


#exit
prelude

inductive eq {α : Sort*} (a : α) : α → Sort
| refl : eq a

infix ` = `:50 := eq

constant nat : Type

constant nat.zero : nat

constant nat.succ : nat → nat

constant cast {α : Sort*} (zero : α) (succ : α → α) : nat → α

constant cast_zero {α : Sort*} (zero : α) (succ : α → α) : cast zero succ nat.zero = zero

constant cast_succ {α : Sort*} (zero : α) (succ : α → α) (n : nat) :
  cast zero succ (nat.succ n) = succ (cast zero succ n)

constant cast_unique {α : Sort*} (zero : α) (succ : α → α)
  (f : nat → α) (hzero : f nat.zero = zero)
  (hsucc : ∀ n, f (nat.succ n) = succ (f n)) :
  ∀ n, f n = cast zero succ n

lemma nat.rec_on {C : nat → Sort*} (n : nat)
  (hzero : C nat.zero)
  (hsucc : Π (a : nat), C a → C (nat.succ a)) :
  C n :=
cast _ _ _

#exit
import category_theory.functor_category
open category_theory
open category_theory.category
universes v₁ v₂ u₁ u₂



namespace tactic.interactive

meta def poor_mans_rewrite_search : tactic unit :=
`[    iterate 5
    { repeat {rw assoc},
      try {rw nat_trans.naturality},
      try {simp},
      repeat {rw ←assoc},
      try {rw nat_trans.naturality},
      try {simp}
    }]

end tactic.interactive

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

variables (X Y U V: C)
variables (f : X ⟶ Y) (g : V ⟶ U)(h : Y ⟶ V)
variables (F G  : C ⥤ D)
variables (α : F ⟶ G)

/- The diagram coming from g and α
    F(f)        F(h)       F(g)
F X ---> F Y  --->  F V   ----> F U
 |        |           |          |
 |α(X)    |α(Y)       | α (v)    |  α (U)
 v        v           v          v
G X ---> G Y ---->    G(V) ---- G(U)
    G(f)       G(h)         G(g)
commutes.
-/



example :
  F.map f ≫  α.app Y ≫ G.map h ≫  G.map g =
    F.map f ≫ F.map h ≫ α.app V  ≫ G.map g :=
begin
  poor_mans_rewrite_search,
end
#exit
import data.equiv.basic
#

axiom univalence {α β : Sort*} : α ≃ β → α = β




#exit
--import tactic.suggest
import data.nat.basic algebra.group_power tactic.ring

lemma X1 (a b : ℤ) : a + (a + (a + b)) = a * 3 + b := by ring

--lemma X2 (a b : ℤ) : (a * (a * (a * (a * b))))

example (a b c x : ℤ) (hx : x^3 = -3) :
  (a * x^2 + b * x + c)^3 =
  - 9 * a^2 * b * x^2
  + 3 * a * c^2 * x^2 +
  3 * b^2 * c * x^2
   +

  3 * b * c^2 * x
  - 9 * a * b^2 * x
  - 9 * a^2 * c * x

  + 9 * a ^ 3
  -3 * b^3
  - 18 * a * b * c
  + c^3 :=
begin
  simp [pow_succ, mul_add, add_mul, mul_assoc, mul_comm,
    mul_left_comm] at *,
  simp only [← mul_assoc, ← add_assoc],
  have : ∀ y, x * (x * (x * y)) = -3 * y, { intro, rw [← hx], ring },
  simp [hx, this],
  ring,

end

local attribute [simp] nat.succ_pos'

set_option trace.simplify.rewrite true



def ack : ℕ → ℕ → ℕ
| 0     y     := y+1
| (x+1)  0    := ack x 1
| (x+1) (y+1) := ack x (ack (x+1) y)
using_well_founded {rel_tac := λ _ _, `[exact ⟨λ _ _, true, sorry⟩],
  dec_tac := `[trivial]}

#eval ack 3 5

#exit
import category_theory.monoidal.types

#reduce terminal Type

#exit
import data.zmod.basic data.nat.totient group_theory.order_of_element
local notation `φ` := nat.totient

open fintype finset

instance {n : ℕ+} : fintype (units (zmod n)) :=
fintype.of_equiv _ zmod.units_equiv_coprime.symm

lemma card_units_eq_totient (n : ℕ+) :
  card (units (zmod n)) = φ n :=
calc card (units (zmod n)) = card {x : zmod n // x.1.coprime n} :
  fintype.card_congr zmod.units_equiv_coprime
... = φ n : finset.card_congr
  (λ a _, a.1.1)
  (λ a, by simp [a.1.2, a.2.symm] {contextual := tt})
  (λ _ _ h, by simp [subtype.val_injective.eq_iff, (fin.eq_iff_veq _ _).symm])
  (λ b hb, ⟨⟨⟨b, by finish⟩, nat.coprime.symm (by simp at hb; tauto)⟩, mem_univ _, rfl⟩)

lemma pow_totient {n : ℕ+} (x : units (zmod n)) : x ^ φ n = 1 :=
by rw [← card_units_eq_totient, pow_card_eq_one]

@[simp] lemma totient_zero : φ 0 = 0 := rfl

def coprime.to_units {n : ℕ+} {p : ℕ} (h : nat.coprime p n) : units (zmod n) :=


lemma pow_totient' {n : ℕ+} {p : ℕ} (h : nat.coprime p n) : p ^ φ n ≡ 1 [MOD n] :=
begin
  cases n, { simp },
  { erw [← @zmod.eq_iff_modeq_nat ⟨n.succ, nat.succ_pos _⟩, nat.cast_pow],
    let x := zmod.units_equiv_coprime.symm.to_fun
      ⟨(p : zmod ⟨n.succ, nat.succ_pos _⟩), by simpa using h⟩, }




end


#exit
import tactic.ring linear_algebra.basic linear_algebra.dual

variables {R : Type*} [field R]
open finset

example {R : Type*} [ring R] (x₁ x₂ y₁ y₂ : R) :
  Σ' z₁ z₂ : R, z₁ ^ 2 + z₂ ^ 2 = (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) :=
⟨x₁ * y₁ + x₂ * y₂, x₁ * y₂ - x₂ * y₁, begin
  simp only [mul_add, add_mul, add_comm, add_right_comm, pow_two,
    sub_eq_add_neg],
  simp only [(add_assoc _ _ _).symm],

end⟩

example {n : ℕ}
  (hn : ∀ x₁ x₂ : fin (2 ^ n) → R, ∃ y : fin (2 ^ n) → R,
    univ.sum (λ i, y i ^2) = univ.sum (λ i, x₁ i ^ 2) * univ.sum (λ i, x₂ i ^ 2)) :



#exit
import data.polynomial

open polynomial
#print is_unit
example (A B : Type) [comm_ring A] [comm_ring B] (f : A →+* B)
  (p : polynomial A) (hp : monic p) (hip : irreducible (p.map f)) :
  irreducible p :=
classical.by_contradiction $ λ h,
  begin
    dsimp [irreducible] at h,
    push_neg at h,
    cases h,
    { sorry },
    { rcases h with ⟨q, r, hpqr, hq, hr⟩,
      have := hip.2 (q.map f) (r.map f) (by rw [← map_mul, hpqr]),
       }



  end


#exit
inductive eq2 {α : Type} (a : α) : α → Type
| refl : eq2 a

lemma X {α : Type} (a b : α) (h₁ h₂ : eq2 a b) : eq2 h₁ h₂ :=
begin
  cases h₁, cases h₂, exact eq2.refl _,

end
set_option pp.proofs true
#print X

inductive X : Type
| mk : X → X

example : ∀ x : X, false :=
begin
  assume x,
  induction x,

end

instance : fintype X := ⟨∅, λ x, X.rec_on x (λ _, id)⟩

#print X.rec

inductive Embedding (b a:Sort u) : Sort u
| Embed : forall (j:b -> a), (forall (x y:b), j x = j y -> x = y) -> Embedding
#print Embedding.rec
def restrict {a b:Sort u} (r:a -> a -> Prop) (e:Embedding b a) (x y: b) : Prop :=
  begin
   destruct e, -- error
  end

#print Embedding

#exit
def injective {X : Type} {Y : Type} (f : X → Y) : Prop :=
  ∀ a b : X, f a = f b → a = b

theorem injective_comp3 {X Y Z : Type} (f : X → Y) (g : Y → Z) :
  injective f → injective g → injective (g ∘ f) :=
λ hf hg _ _, (hf _ _ ∘ hg _ _)
--   dunfold injective,
--   intros hf hg a b,


-- end

#exit
import data.list data.equiv.basic data.fintype
noncomputable theory
open_locale classical
universe u
variables (α β : Type u)

open finset list

@[simp] lemma list.nth_le_pmap {l : list α} {p : α → Prop}
  (f : Π (a : α), p a → β) (h : ∀ a, a ∈ l → p a) (n : ℕ)
  (hn : n < l.length) :
  (l.pmap f h).nth_le n (by simpa using hn) = f (l.nth_le n hn)
  (h _ (nth_le_mem _ _ _)) :=
by simp [pmap_eq_map_attach]

@[simp] lemma list.nth_le_fin_range {n i : ℕ} (h : i < n) :
  (fin_range n).nth_le i (by simpa using h) = ⟨i, h⟩ :=
by simp only [fin_range]; rw [list.nth_le_pmap]; simp *

lemma fin_range_map_nth_le {l : list α} :
  (list.fin_range l.length).map (λ x, l.nth_le x.1 x.2) = l :=
list.ext_le (by simp) (λ _ _ _, by rw [nth_le_map, list.nth_le_fin_range])

lemma length_filter_eq_card_fin {l : list α} (p : α → Prop) :
  list.length (list.filter p l) =
    (univ.filter (λ x : fin l.length, p (l.nth_le x.1 x.2))).card :=
calc list.length (list.filter p l)
    = (((list.fin_range l.length).map (λ x : fin l.length, l.nth_le x.1 x.2)).filter p).length :
  by rw [fin_range_map_nth_le]
... = ((list.fin_range l.length).filter (λ x : fin l.length, p (l.nth_le x.1 x.2))).length :
    by rw [filter_of_map, length_map]
... = (finset.mk
    ((list.fin_range l.length).filter (λ x : fin l.length, p (l.nth_le x.1 x.2)))
    (list.nodup_filter _ (nodup_fin_range _))).card : rfl
... = _ : congr_arg card (finset.ext.2 (by simp))

lemma card_filter_univ [fintype α] (p : α → Prop) :
  card (univ.filter p) = fintype.card (subtype p) :=
begin
  refine (finset.card_congr (λ a _, ↑a) _ _ _).symm,
  { rintros ⟨_, h⟩ _; simp * },
  { rintros ⟨_, _⟩ ⟨_, _⟩; simp },
  { intros b hb,
    refine ⟨⟨b, (finset.mem_filter.1 hb).2⟩, by simp⟩, }
end
#print classical.axiom_of_choice
example {α : Sort*} {β : α → Sort*} :
  (∀ a, nonempty (β a)) ↔ nonempty (Π a, β a) :=
by library_search

example {l₁ l₂ : list β} {r : α → β → Prop}
  (nodup : ∀ (x y : α) (b : β), x ≠ y → ¬ (r x b ∧ r y b))
  (h : ∀ a : α, l₁.countp (r a) = l₂.countp (r a)) :
  l₁.countp (λ b, ∃ a, r a b) = l₂.countp (λ b, ∃ a, r a b) :=
begin
  simp only [countp_eq_length_filter, length_filter_eq_card_fin,
    card_filter_univ, fintype.card_eq, skolem_nonempty] at *,
  cases h with f,
  split,
  exact ⟨λ x, ⟨f x, _⟩, _, _, _⟩





end


#exit
prelude
import init.logic
set_option old_structure_cmd true

universe u

class comm_semigroup (α : Type u) extends has_mul α

class monoid (α : Type u) extends has_mul α, has_one α :=
(one_mul : ∀ a : α, 1 * a = a)

class comm_monoid (α : Type u) extends comm_semigroup α, has_one α :=
(one_mul : ∀ a : α, 1 * a = a)

set_option pp.all true

class X (α : Type u) extends monoid α, comm_monoid α

#exit
--import data.real.basic

def injective (f : ℤ → ℤ ) := ∀ x x', f x = f x' → x = x'

example (f g : ℤ → ℤ) :
  injective f → injective g → injective (g ∘ f) :=
begin
  intros hf hg x x' gof,
  rw hf x,
  rw hg (f x),
  exact gof,
end

open finset

open_locale classical

example {α β : Type} {x : α} {v : β → α} [comm_monoid α] [fintype β] :
  finset.univ.prod (λ (i : option β), i.elim x v) = x * finset.univ.prod v :=
calc univ.prod (λ (i : option β), i.elim x v)
    = x * (univ.erase (none)).prod (λ (i : option β), i.elim x v) :
  begin
    conv_lhs { rw [← insert_erase (mem_univ (none : option β))] },
    rw [prod_insert (not_mem_erase _ _)], refl
  end
... = x * finset.univ.prod v :
  begin
    refine congr_arg2 _ rfl (prod_bij (λ a _, some a) _ _ _ _).symm,
    { simp },
    { intros, refl },
    { simp },
    { assume b,
      cases b with b,
      { simp },
      { intro, use b, simp } }
  end

import data.zmod.quadratic_reciprocity

open finset

def Fib : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n + 2) := Fib n + Fib (n + 1)

theorem sum_Fib (n : ℕ) : 1 + (range n).sum Fib = Fib (n + 1) :=
by induction n; simp [sum_range_succ, Fib, *]
#print sum_Fib
#exit
import algebra.group_power tactic.ring

example (x y : ℤ) : y^4 + 9 * y^2 + 20 ≠ x^3 :=
suffices (y^2 + 5) * (y^2 + 4) ≠ x^3,
  by ring at *; assumption,
assume h : (y^2 + 5) * (y^2 + 4) = x^3,


#exit
import data.finset

set_option profiler true

#eval (finset.range 200).filter (λ x, x % 2 = 0)


def has_min_element {A : Type} (R : A → A → Prop) : Prop :=
    ∃ x, ∀ y, R x y
axiom ax1 {n m: ℕ} : (n ≤ m) ↔ (∃ l : ℕ, n + l = m)
axiom ax2 {m n x y: ℕ} (h1 : x + n = y) (h2 : y + m = x): x = y ∧ (m = 0) ∧ (n = 0)
axiom ax3 {m n x y z : ℕ} (h1 : x + n = y) (h2 : y + m = z) : x + (n + m) = z
axiom ax4 : 1 ≠ 2
axiom ax5 (m n : ℕ) : ∃ l : ℕ, m + l = n ∨ n + l = m
axiom ax6 (n : ℕ) : 0 + n = n

theorem le_not_symmetric : ¬ (symmetric nat.less_than_or_equal) :=
λ h, absurd (@h 0 1 dec_trivial) dec_trivial

example : ¬ (equivalence nat.less_than_or_equal) :=
λ h, le_not_symmetric h.2.1

variables (U : Type) (P R: U → Prop)(Q : Prop)
example (h1a : ∃ x, P x) (h1b : ∃ x, R x) (h2 : ∀ x y, P x → R y → Q) : Q :=
begin
  cases h1a with x hPx,
  cases h1b with y hRy,
end

#eval (finset.range 10000).filter
  (λ y, ∃ x ∈ finset.range (nat.sqrt y), y^2 + 9 * y + 20 = x)

-- #eval let n  : ℕ+ := 511 in (finset.univ).filter
--   (λ y : zmod n, ∃ x, y^4 + 9 * y ^ 2 + 20 = x)


example (a b s : ℚ) (hs : s * s = -35):
  (a + b * (1 + s)/ 2)^3 =
  a^3 + 3 * a^2 * b / 2 - 51 * a * b^2 / 2 - 13 * b ^ 3
  + (3 * a^2 * b /2+ 3 * a * b ^ 2 /2- 4 * b^3) * s:=
begin
  simp [pow_succ, mul_add, add_mul, mul_comm s, mul_assoc,
    mul_left_comm s, hs, div_eq_mul_inv],
  ring,
  -- simp [bit0, bit1, mul_add, add_mul, add_assoc, add_comm,
  --   add_left_comm, mul_assoc, mul_comm, mul_left_comm],


end

#eval (finset.univ : finset (zmod 24 × zmod 24)).image
  (λ x : zmod 24 × zmod 24, x.1^2 + 6 * x.2^2 )

#exit


import data.list
noncomputable theory
open_locale classical
universe u
variables {α : Type u} (a : α) (l : list α)

theorem count_eq_countp {h : decidable_pred (λ x, a = x)} :
  l.count a = l.countp (λ x, a = x) := sorry
theorem count_eq_countp' : l.count a = l.countp (λ x, x = a) :=
begin
  conv in (_ = a) { rw eq_comm, },
  convert (count_eq_countp a l), -- error here
end
#exit
import data.nat.parity
open nat




example {x y : ℕ} : even (x^2 + y^2) ↔ even (x + y) :=
by simp [show 2 ≠ 0, from λ h, nat.no_confusion h] with parity_simps

#exit
import ring_theory.ideals algebra.associated

open ideal

local infix ` ≈ᵤ `: 50 := associated

variables {R : Type*} [integral_domain R]
  (wf : well_founded (λ x y : R, span {y} < span ({x} : set R)))
  (hex : ∀ p q : R, irreducible p → irreducible q → ¬ p ≈ᵤ q →
    ∃ x : R, x ∈ span ({p, q} : set R) ∧ x ≠ 0 ∧ x ≠ p ∧ x ≠ q ∧
      (span {p} < span ({x} : set R) ∨ span {q} < span ({x} : set R)))

lemma exists_irreducible_factor {a : R} (hau : ¬ is_unit a) :
  ∃ p, irreducible p ∧ p ∣ a := sorry

include hex

example (a b : R) : ∀ (p q : R) (hp : irreducible p) (hq : irreducible q) (hpq : ¬ p ≈ᵤ q)
  (hpa : p * b = q * a), p ∣ a :=
have ¬ is_unit a, from sorry,
well_founded.fix wf
begin
  assume a ih p q hp hq hpq hpa,
  cases exists_irreducible_factor this with r hr,
  cases hex p q hp hq hpq with x hx,
  have : span ({a} : set R) < span {x},
    from hx.2.2.2.2.elim
      (lt_of_le_of_lt sorry)
      (lt_of_le_of_lt _),

end a




#exit
import data.nat.prime

open nat

theorem sqrt_two_irrational_V1 {a b : ℕ} (co : gcd a b = 1) : a^2 ≠ 2 * b^2 :=
assume h : a^2 = 2 * b^2,
have 2 ∣ a^2,
    by simp [h],
have ha : 2 ∣ a,
    from prime.dvd_of_dvd_pow prime_two this,
-- this line below is wrong
match ha with | ⟨c, aeq⟩ :=
have 2 * (2 * c^2) = 2 * b^2,
    by simp [eq.symm h, aeq];
       simp [nat.pow_succ, mul_comm, mul_assoc, mul_left_comm],
have 2 * c^2 = b^2,
    from eq_of_mul_eq_mul_left dec_trivial this,
have 2 ∣ b^2,
    by simp [eq.symm this],
have hb : 2 ∣ b,
    from prime.dvd_of_dvd_pow prime_two this,
have 2 ∣ gcd a b,
    from dvd_gcd ha hb,
have habs : 2 ∣ (1:ℕ),
    by simp * at *,
show false, from absurd habs dec_trivial
end
#print sqrt_two_irrational_V1

#exit
example (A B : Prop) : A → (A ∧ B) ∨ (A ∧ ¬ B) :=
assume a : A,
  classical.by_contradiction
    (assume h : ¬((A ∧ B) ∨ (A ∧ ¬ B)),
      have nb : ¬ B, from
        assume b : B,
          h (or.inl ⟨a, b⟩),
      h (or.inr ⟨a, nb⟩))

#exit
import logic.basic
#print eq.drec_on
axiom choice (X : Type) : X ⊕ (X → empty)

def choice2 {α : Type} {β : α → Type*} (h : ∀ x, nonempty (β x)) :
  nonempty (Π x, β x) :=
⟨λ x, sum.cases_on (choice (β x)) id
  (λ f, false.elim (nonempty.elim (h x) (λ y, empty.elim (f y))))⟩


#exit
import data.sum linear_algebra.basic

example {α α' β β' : Type} (f : α → α') (g : β → β') :
  α ⊕ β → α' ⊕ β'
| (sum.inl a) := sum.inl (f a)
| (sum.inr b) := sum.inr (g b)

example {A A' B B' : Type} [add_comm_group A]
  [add_comm_group A'] [add_comm_group B] [add_comm_group B']
  (f : A →+ A') (g : B →+ B') :
  A × A' → B × B'

lemma inv_unique {x y z : M}
  (hy : x * y = 1) (hz : z * x = 1) : y = z :=
by rw [← one_mul y, ← hz, mul_assoc, hy, mul_one]



#exit




import data.pfun

import data.list.defs

namespace tactic

meta def match_goals (ls : list (ℕ × ℕ)) : tactic unit := do
  gs ← get_goals,
  ls.mmap' $ λ ⟨a, b⟩, unify (gs.inth a) (gs.inth b),
  set_goals gs
#print tactic.interactive.induction
meta def interactive.cases_symmetric
  (a b : interactive.parse (lean.parser.pexpr std.prec.max)) : tactic unit := do
  a ← to_expr a,
  b ← to_expr b,
  env ← get_env,
  ty ← infer_type a,
  let n := (env.constructors_of ty.get_app_fn.const_name).length,
  (() <$ cases_core a [`a]); (() <$ cases_core b [`a]),
  match_goals $ do
    a ← list.range n,
    b ← list.range n,
    guard (b < a),
    return (n * a + b, n * b + a)
end tactic

inductive weekday
| sun | mon | tue | wed | thu | fri | sat

example : weekday → weekday → nat :=
begin
  intros a b,
  cases_symmetric a b,
end




import init.data.nat.basic
import init.algebra.ring
import data.nat.parity
import init.algebra.norm_num
import data.equiv.list
import tactic.omega
import data.W
#print int.sizeof
#print subtype.range_val
#print W
def N : Type := W (λ b : bool, bool.cases_on b empty unit)

def F : N → ℕ := λ n, W.rec_on n
  (λ b, bool.cases_on b (λ _ _, 0) (λ _ f, nat.succ (f ())))

def G : ℕ → N := λ n, nat.rec_on n
  (W.mk ff empty.elim)
  (λ _ ih, W.mk tt (λ _, ih))

lemma FG (n : ℕ) : F (G n) = n :=
nat.rec_on n rfl
  (begin
    dsimp [F, G],
    assume n h,
    rw h,
  end)

lemma GF (n : N) : G (F n) = n :=
W.rec_on n
  (λ b, bool.cases_on b
    (λ b _, begin
      have h : b = (λ x, empty.elim x), from funext (λ x, empty.elim x),
      simp [G, F, h], refl,
    end)
    (λ f, begin
      dsimp [F, G],
      assume ih,
      rw ih (),
      congr, funext, congr,


    end))

open finset
example {s : finset ℕ} (x : ℕ) (h : x ∈ s) : s \ {x} ⊂ s :=
finset.ssubset_iff.2 ⟨x, by simp,
  λ y hy, (mem_insert.1 hy).elim (λ hxy, hxy.symm ▸ h) (by simp {contextual := tt})⟩

#eval denumerable.equiv₂ ℕ (ℕ × ℕ × ℕ × ℕ × ℕ) 15
3192
#eval 2^12

--Alice only sees r and Bob only sees c. The strategy isn't (r,c) → (...) but two maps, r→(r1 r2 r3) and c → (c1 c2 c3)
--I'm using 0 and 1 instead of Green and Red as the two options to fill squares. This makes checking parity of strategies easier
open nat
def checkStrategyrc (r c : ℕ) (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : Prop :=
--functionalize this with lists.
let r1 := (strategy.1 r).1,
r2 := (strategy.1 r).2.1,
r3 := (strategy.1 r).2.2,
c1 := (strategy.2 c).1,
c2 := (strategy.2 c).2.1,
c3 := (strategy.2 c).2.2

    in even (r1 + r2 + r3) ∧ ¬ even (c1 + c2 + c3) ∧
    ((r = 1 ∧ c = 1 ∧ r1 = c1) ∨ (r = 1 ∧ c = 2 ∧ r2 = c1) ∨ (r = 1 ∧ c = 3 ∧ r3 = c1)
    ∨(r = 2 ∧ c = 1 ∧ r1 = c2) ∨ (r = 2 ∧ c = 2 ∧ r2 = c2) ∨ (r = 2 ∧ c = 3 ∧ r3 = c2)
    ∨(r = 3 ∧ c = 1 ∧ r1 = c3) ∨ (r = 3 ∧ c = 2 ∧ r2 = c3) ∨ (r = 3 ∧ c = 3 ∧ r3 = c3))
--checks all three conditions are met for the strategy
def checkStrategy (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : Prop :=
(checkStrategyrc 1 1 strategy) ∧ (checkStrategyrc 1 2 strategy) ∧ (checkStrategyrc 1 3 strategy) ∧
(checkStrategyrc 2 1 strategy) ∧ (checkStrategyrc 2 2 strategy) ∧ (checkStrategyrc 2 3 strategy) ∧
(checkStrategyrc 3 1 strategy) ∧ (checkStrategyrc 3 2 strategy) ∧ (checkStrategyrc 3 3 strategy)



instance : decidable_pred checkStrategy :=
λ _, by dunfold checkStrategy checkStrategyrc even; apply_instance

-- theorem notnoStrategy : ∃ (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))),
--   (checkStrategy (strategy)) :=
-- ⟨(λ _, (0, 0, 0), λ _, (0, 0, 0)), dec_trivial⟩

-- --someone on Zulip said to try putting this not directly after the import statements. This seems to have helped
-- open_locale classical
-- --given a strategy, we can't have it satisfy all the conditions
theorem noStrategy2 (strategy : ((ℕ → ℕ × ℕ × ℕ) × (ℕ → ℕ × ℕ × ℕ))) : ¬ (checkStrategy (strategy)) :=
begin
  dsimp [checkStrategy, checkStrategyrc],
  simp only [eq_self_iff_true, true_and,
    (show (1 : ℕ) ≠ 2, from dec_trivial),
    (show (1 : ℕ) ≠ 3, from dec_trivial),
    false_and, false_or, or_false,
    (show (3 : ℕ) ≠ 1, from dec_trivial),
    (show (3 : ℕ) ≠ 2, from dec_trivial),
    (show (2 : ℕ) ≠ 1, from dec_trivial),
    (show (2 : ℕ) ≠ 3, from dec_trivial)],
  generalize h : strategy.1 0 = x₁,
  generalize h : strategy.1 1 = x₂,
  generalize h : strategy.1 2 = x₃,
  generalize h : strategy.1 3 = x₄,
  generalize h : strategy.2 0 = y₁,
  generalize h : strategy.2 1 = y₂,
  generalize h : strategy.2 2 = y₃,
  generalize h : strategy.2 3 = y₄,
  clear h h h h h h h h strategy,
  rcases x₁ with ⟨_, _, _⟩,
  rcases x₂ with ⟨_, _, _⟩,
  rcases x₃ with ⟨_, _, _⟩,
  rcases x₄ with ⟨_, _, _⟩,
  rcases y₁ with ⟨_, _, _⟩,
  rcases y₂ with ⟨_, _, _⟩,
  rcases y₃ with ⟨_, _, _⟩,
  rcases y₄ with ⟨_, _, _⟩,
  simp with parity_simps,
  simp only [iff_iff_implies_and_implies],
  finish,


end

example : true := trivial

#eval (∃ f : (vector (fin 2 × fin 2 × fin 2) 3 × vector (fin 2 × fin 2 × fin 2) 3),
    (checkStrategy (λ n, ((f.1.nth (n - 1)).map fin.val) (prod.map fin.val fin.val),
    λ n, ((f.2.nth (n - 1)).map fin.val) (prod.map fin.val fin.val))) : bool)



#exit
import algebra.pointwise
import ring_theory.algebra

local attribute [instance] set.smul_set_action

variables (R : Type*) [comm_ring R]

variables (A : Type*) [ring A] [algebra R A]
set_option class.instance_max_depth 26
example : mul_action R (set A) :=
by apply_instance -- works

variables (B : Type*) [comm_ring B] [algebra R B]

set_option trace.class_instances true
set_option class.instance_max_depth 34
example : mul_action R (set B) :=
by apply_instance -- fails


import data.finset data.int.sqrt data.nat.parity data.complex.exponential

example : finset ℤ := by library_search

example (n : ℕ) : finset ℤ := finset.map ⟨int.of_nat, @int.of_nat.inj⟩
  (finset.range n)

#exit
import data.quot data.setoid

meta def quotient_choice {α β : Type} [s : setoid β]
  (f : α → quotient s) : quotient (@pi_setoid _ _ (λ a : α, s)) :=
quotient.mk (λ a : α, quot.unquot (f a))

--applying choice to the identity map
def decidable_true
  (quotient_choice : Π {α β : Type} [s : setoid β]
    (f : α → quotient s), quotient (@pi_setoid _ _ (λ a : α, s))) :
  decidable true :=
-- ⊤ is the always true relation
by letI : setoid bool := ⊤; exact
quot.rec_on_subsingleton (@quotient_choice (@quotient bool ⊤) bool ⊤ id)
  (λ f, decidable_of_iff (f ⟦ff⟧ = f ⟦tt⟧)
    (iff_true_intro (congr_arg f (quotient.sound trivial))))

#eval decidable_true @quotient_choice

#exit
import data.quot

variables {A : Type} {B : A → Type}

example (f : Π a : A, trunc (sigma B)) :
  trunc (Π a : A, sigma B) :=


#exit
import data.set.basic data.set.lattice

example {s t : set ℕ} : s < t ↔ s ⊂ t := iff.rfl
example {s t : set ℕ} : s ≤ t ↔ -s ≤ -t := by library_search
set_option class.instance_max_depth 1000

local attribute

def decidable_true (choice : Π {α : Type*} {β : α → Type*}
  (f : Π a, @quotient (β a) ⊤), @quotient (Π a, β a) ⊤) : decidable true :=
quot.rec_on_subsingleton (choice (id : @quotient bool ⊤ → @quotient bool ⊤))
  (λ f, decidable_of_iff (f (quotient.mk' ff) = f (quotient.mk' tt))
    (iff_true_intro (congr_arg f (quotient.sound' (by constructor))))

example : @quotient.choice (@quotient bool ⊤) (λ _, @quotient bool ⊤)
  ()

#exit
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.nat.basic data.fintype
import tactic

/-!
# Strong recursion

A strong recursion principle based on `fin`.
The benefit of `(Π (m:fin n), X m)` over `Π (m:ℕ) (h:m < n), X m`
is that with `fin` the bound on `m` is bundled,
and this can be used in later proofs and constructions.

## Example

For example, one can use this to give a definition of the Bernoulli numbers
that closely follows the recursive definition found at
https://en.wikipedia.org/wiki/Bernoulli_number#Recursive_definition
It is:
$$ B_n = 1 - \sum_{k < n} \binom{n}{k} \frac{B_k}{n - k + 1} $$

```
example : ℕ → ℚ :=
strong_recursion $ λ n bernoulli,
1 - finset.univ.sum (λ k : fin n, (n.choose k) * bernoulli k / (n - k + 1))
```

This example shows the benefit of using `fin n` in the implementation,
because it allows us to use `finset.univ.sum` which enables the recursive call `bernoulli k`.
If, on the other hand, we had used `Π (m:ℕ) (h:m < n), X m` and `(finset.range n).sum`,
then the recursive call to `bernoulli k` would get stuck,
because it would come with a proof obligation `k < n`
which isn't provided by `(finset.range n).sum`.

-/

namespace nat
universe variable u
variables {X : ℕ → Sort u} (f : Π n, (Π (m:fin n), X m) → X n)

/-- A strong recursion principle for the natural numbers.
It allows one to recursively define a function on ℕ
by showing how to extend a function on `fin n := {k // k < n}` to `n`. -/
def strong_recursion : Π n : ℕ, X n
| n := f _ (λ k : fin n, have wf : ↑k < n, from k.2, strong_recursion ↑k)

lemma strong_recursion_apply (n : ℕ) :
  strong_recursion f n = f n (λ i, strong_recursion f i) :=
by rw strong_recursion

-- Example: Fibonacci
example : ℕ → ℚ :=
strong_recursion $ λ n fib,
match n, fib with
| 0 := λ _, 0
| 1 := λ _, 1
| (k+2) := λ fib, fib k + fib (k+1)
end


-- Example: Bernoulli
def bernoulli₁ : ℕ → ℚ :=
strong_recursion $ λ n bernoulli,
1 - finset.univ.sum (λ k : fin n, (n.choose k) * bernoulli k / (n - k + 1))

def bernoulli (n : ℕ) : ℚ :=
well_founded.fix nat.lt_wf
  (λ n bernoulli, 1 - finset.univ.sum
    (λ k : fin n, (n.choose k) * bernoulli k k.2 / (n - k + 1))) n

#eval (λ k, bernoulli₂ k - bernoulli₁ k) 8

end nat
#exit
import logic.basic

open classical
variables (α : Type) (p q : α → Prop)
variable a : α
#print classical.not_forall
local attribute [instance] classical.prop_decidable
theorem T08R [∀ x, decidable (p x)] (h : (¬ ∀ x, p x) → (∃ x, ¬ p x)) :
  (∃ x, ¬ p x) ∨ ¬ (∃ x, ¬ p x) :=
begin


end

#exit
import data.nat.basic

open nat

lemma choose_mul_succ_eq (n k : ℕ) :
  (n.choose k) * (n + 1) = ((n+1).choose k) * (n + 1 - k) :=
begin
  by_cases hkn : k ≤ n,
  { have pos : 0 < fact k * fact (n - k), from mul_pos (fact_pos _) (fact_pos _),
    rw [← nat.mul_left_inj pos],
    suffices : choose n k * fact k * fact (n - k) * (n + 1) =
      choose (n + 1) k * fact k * ((n + 1 - k) * fact (n - k)),
    { simpa [mul_comm, mul_assoc, mul_left_comm] },
    rw [choose_mul_fact_mul_fact hkn, nat.succ_sub hkn, ← fact_succ,
      ← nat.succ_sub hkn, choose_mul_fact_mul_fact (le_succ_of_le hkn), fact_succ,
      mul_comm] },
  simp [choose_eq_zero_of_lt (lt_of_not_ge hkn), nat.sub_eq_zero_iff_le.2 (lt_of_not_ge hkn)],
end


open classical
variables {α : Type} {p : α → Prop}

theorem T06_1 : ¬ (∀ x, ¬ p x) → (∃ x, p x) :=
    (assume hnAxnpx : ¬ (∀ x, ¬ p x),
        by_contradiction
            (λ hnExpx : ¬ (∃ x, p x),
                (hnAxnpx
                    (λ x, (λ hpx,
                        hnExpx (exists.intro x hpx))))))
#check T06_1
-- it appears this is needed in tactic mode
local attribute [instance] classical.prop_decidable
theorem T06_2 : ¬ (∀ x, ¬ p x) → (∃ x, p x) :=
begin
    intro hnAxnpx,
    by_contradiction,
end

#exit
import topology.separation data.set.finite algebra.associated data.equiv.basic tactic.ring

example {α : Type} {p : α → Prop} (r : Prop): (∀ x, p x ∨ r) → ∀ x, p x ∨ r :=
assume h : ∀ x, p x ∨ r, assume a: α,
  or.elim (h a)
  (assume hl: p a,
    show p a ∨ r, from
      or.inl hl)
  (assume hr: r,
    show p a ∨ r, from or.inr hr)


example {M : Type} [monoid M] {a b c : M} (h : a * b = 1) (h2 : c * a = 1) : b = c :=
by rw [← one_mul b, ← h2, mul_assoc, h, mul_one]

open set
universes u v
variables {X : Type u} [topological_space X] [normal_space X] {α : Type v}
#print function.swap
def T (s : set X) (u : α → set X) : Type (max u v) :=
Σ (i : set α), {v : α → set X // s ⊆ Union v ∧ (∀ a, is_open (v a)) ∧
  (∀ a ∈ i, closure (v a) ⊆ u a) ∧ (∀ a ∉ i, v a = u a)}

def le_aux (s : set X) (u : α → set X) : T s u → T s u → Prop :=
λ t t', t.1 ⊆ t'.1 ∧ ∀ a ∈ t.1, t.2.1 a = t'.2.1 a

instance (s : set X) (u : α → set X) : preorder (T s u) :=
{ le := le_aux s u,
  le_trans := λ ⟨u₁, v₁, hv₁⟩ ⟨u₂, v₂, hv₂⟩ ⟨u₃, v₃, hv₃⟩ ⟨hu₁₂, hv₁₂⟩ ⟨hu₂₃, hv₂₃⟩,
    ⟨set.subset.trans hu₁₂ hu₂₃, λ a ha, (hv₁₂ a ha).symm ▸ hv₂₃ _ (hu₁₂ ha)⟩,
  le_refl := λ t, ⟨set.subset.refl _, λ _ _, rfl⟩ }

open_locale classical

example (s : set X) (u : α → set X)
  (su : s ⊆ Union u) (uo : ∀ a, is_open (u a)) :=
@zorn.exists_maximal_of_chains_bounded (T s u) (≤)
  (λ c hc,
      ⟨⟨⋃ (t : T s u) (ht : t ∈ c), t.1,
        λ a, ⋂ (t : T s u) (ht : t ∈ c), t.2.1 a,
        ⟨begin
          assume x hx,
          simp only [set.mem_Union, set.mem_Inter],
          cases set.mem_Union.1 (su hx) with a ha,
          refine ⟨a, λ t ht, _⟩,
          rwa t.2.2.2.2.2,
        end,
        λ a, is_open_Union (λ t, is_open_Union (λ ht, t.2.2.2.1 _)),
        λ a ha, begin
          simp only [set.mem_Union] at ha,
          rcases ha with ⟨t, htc, ha⟩,
          have := t.2.2.2.2.1 a ha,
          assume x hx, sorry

        end,
        begin
          assume a ha,
          ext,
          simp only [set.mem_Union, not_exists] at *,
          split,
          { rintro ⟨t, htc, ht⟩,
            rwa ← t.2.2.2.2.2 a (ha _ htc) },
          { assume hau,
            cases hcn with t htc,
            use [t, htc],
            rwa t.2.2.2.2.2 _ (ha _ htc) }
        end⟩⟩,
      λ t htc, ⟨λ x hx, set.mem_Union.2 ⟨t, by simp *⟩,
        λ a, begin

        end⟩⟩
    )
  (λ _ _ _, le_trans)

lemma shrinking_lemma
  {s : set X} (hs : is_closed s) (u : α → set X) (uo : ∀ a, is_open (u a))
  (uf : ∀ x, finite {a | x ∈ u a}) (su : s ⊆ Union u) :
  ∃ v : α → set X, s ⊆ Union v ∧ ∀ a, is_open (v a) ∧ closure (v a) ⊆ u a :=

#exit
import data.equiv.encodable

#eval @encodable.choose (ℕ × ℕ) (λ x, x.1 ^2 - 26 * x.2 ^2 = 1 ∧ x.2 ≠ 0) _ _ sorry

#exit
import data.mv_polynomial

def eval_list :

#exit
import data.set.basic

#print set.image_preimage_eq

inductive heq' {α : Type} (a : α) : Π {β : Type}, β → Type
| refl : heq' a

inductive eq' {α : Type} (a : α) : α → Type
| refl : eq' a

lemma eq_of_heq' {α : Type} (a b : α) : heq' a b → eq' a b :=
begin
  assume h,
  cases h,
  constructor,
end
#print eq_of_heq'
#exit
import topology.instances.real
example : continuous (λ x : { x : ℝ × ℝ // x ≠ (0, 0) },
  (x.1.1 * x.1.2) / (x.1.1^2 + x.1.2^2)) :=
continuous.mul
  (continuous.mul
    (continuous_fst.comp continuous_subtype_val)
    (continuous_snd.comp continuous_subtype_val))
  (real.continuous.inv
    (begin
      rintros ⟨⟨x₁, x₂⟩, hx⟩, dsimp,
      rw [ne.def, prod.mk.inj_iff, not_and] at hx,
      dsimp, clear hx,
      refine ne_of_gt _,
      simp at *,
      rcases classical.em (x₁ = 0) with rfl | hx₁,
      { rcases classical.em (x₂ = 0) with rfl | hx₂,
        { exact (hx rfl).elim },
        { exact add_pos_of_nonneg_of_pos (pow_two_nonneg _)
            (by rw pow_two; exact mul_self_pos hx₂) } },
      { exact add_pos_of_pos_of_nonneg
          (by rw pow_two; exact mul_self_pos hx₁)
          (pow_two_nonneg _) }
    end)
    (continuous.add
      ((continuous_pow 2).comp
        (continuous_fst.comp continuous_subtype_val))
      ((continuous_pow 2).comp
        (continuous_snd.comp continuous_subtype_val)) ))

example : continuous_on (λ x, x⁻¹ : ℝ → ℝ)
  (≠ 0) := by library_search
#print real.continuous_inv
example : continuous_on (λ x : ℝ × ℝ,
  (x.1 * x.2) / (x.1^2 + x.2^2)) (≠ (0, 0)):=
continuous_on.mul
  (continuous_on.mul
    real.continuous_on
    _)
  (continuous_on.inv)

#exit
example (A B : Prop) : (¬ A ∧ ¬ B) ∨ (A ∧ B) ↔ (A ∨ B) ∧ ()

#exit
import set_theory.ordinal algebra.euclidean_domain
universe u
variables {α : Type u} (r : α → α → Prop) (wf : well_founded r)

lemma psigma.lex.is_well_order {α : Type*} {β : α → Type*}
  (r : α → α → Prop) (s : Π a, β a → β a → Prop) [is_well_order α r]
  [∀ a, is_well_order (β a) (s a)] :
  is_well_order (psigma β) (psigma.lex r s) :=
{  }

noncomputable def rank : α → ordinal.{u}
| a := ordinal.sup.{u u} (λ b : {b : α // r b a},
  have wf : r b.1 a, from b.2, ordinal.succ.{u} (rank b.1))
using_well_founded {rel_tac := λ _ _, `[exact ⟨r, wf⟩],
  dec_tac := tactic.assumption}

lemma mono : ∀ {a b : α}, r a b → rank r wf a < rank r wf b
| a := λ b hab, begin
  rw [rank, rank],
  refine lt_of_not_ge _,
  assume hle,
  rw [ge, ordinal.sup_le] at hle,
  have := hle ⟨_, hab⟩,
  rw [ordinal.succ_le, ← not_le, ordinal.sup_le, classical.not_forall] at this,
  rcases this with ⟨c, hc⟩,
  rw [ordinal.succ_le, not_lt] at hc,
  exact have wf : _ := c.2, not_le_of_gt (mono c.2) hc
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨r, wf⟩], dec_tac := tactic.assumption}

def well_order : Π a b : Σ' a : α, {b // rank r wf b = rank r wf a}, Prop :=
psigma.lex well_ordering_rel (λ _, rank r wf ∘ subtype.val ⁻¹'o (<))

#print psigma.lex

#exit
import order.bounded_lattice

instance : partial_order ℕ := linear_order.to_partial_order ℕ

lemma exampl : well_founded ((<) : with_top ℕ → with_top ℕ → Prop) :=
with_top.well_founded_lt nat.lt_wf

#print axioms exampl

#exit
import data.zmod.basic data.matrix.basic order.filter

variables {p : ℕ → Prop} [decidable_pred p]

def rel' (p : ℕ → Prop) : ℕ → ℕ → Prop :=
λ a b, ∀ n, p n → (∀ m, p m → n ≤ m) → a ≤ n ∧ b < a

def exists_least_of_exists {n : ℕ} (h : p n) : ∃ m, p m ∧ ∀ k, p k → m ≤ k :=
begin
  resetI,
  induction n with n ih generalizing p,
  { exact ⟨0, h, λ _ _, nat.zero_le _⟩ },
  { cases @ih (p ∘ nat.succ) _ h with m hm,
    by_cases hp0 : p 0,
    { exact ⟨0, hp0, λ _ _, nat.zero_le _⟩ },
    { use [m.succ, hm.1],
      assume k hpk,
      cases k with k,
      { contradiction },
      exact nat.succ_le_succ (hm.2 k hpk) } }
end

#print axioms with_top.well_founded_lt

lemma rel'_wf (h : ∃ n, p n) : well_founded (rel' p) :=
begin
  cases h with n hn,
  cases exists_least_of_exists hn with m hm,
  clear hn n,
  refine @subrelation.wf _ (measure (λ a, m - a)) _ _ (measure_wf _),
  assume a b hab,
  rcases hab m hm.1 hm.2 with ⟨ham, hba⟩,
  clear hm hab,
  show m - a < m - b,
  induction ham with z,
  rw nat.sub_self,
  exact nat.sub_pos_of_lt hba,
  rw [nat.succ_sub ham_a, nat.succ_sub],
  exact nat.succ_lt_succ ham_ih,
  exact le_trans(le_of_lt hba) ham_a,
end

attribute [elab_as_eliminator] well_founded.fix

#print axioms le_of_not_gt

lemma nat.lt_of_le_of_ne  {a b : ℕ} (hle : a ≤ b) (hne : a ≠ b) : a < b :=
begin
  induction hle,
  { exact (hne rfl).elim },
  exact nat.lt_succ_of_le hle_a
end

def find (h : ∃ n, p n) : {n // p n ∧ ∀ m, p m → n ≤ m} :=
well_founded.fix (rel'_wf h)
  (λ n ih hn, if hpn : p n then ⟨n, hpn, hn⟩
    else ih n.succ (λ k hk h, ⟨nat.succ_le_of_lt (nat.lt_of_le_of_ne (hn _ hk)
        (by rintro rfl; exact (hpn hk).elim)), nat.lt_succ_self _⟩)
      (λ m hm, nat.succ_le_of_lt (nat.lt_of_le_of_ne (hn _ hm)
      (by rintro rfl; exact (hpn hm).elim)))) 0
  (show ∀ m, p m → 0 ≤ m, from λ _ _, nat.zero_le _)
set_option profiler true
#eval @find     (> 1000000) _ sorry
#eval @nat.find (> 1000000) _ sorry
#print axioms find

#eval (6/10 : zmodp 5 (by norm_num))

#exit
import set_theory.ordinal tactic

lemma exampl {α β : Type} (f : α → β) (hf : function.surjective f) : function.injective (set.preimage f) :=
λ s t, begin
  simp only [set.ext_iff],
  assume h x,
  rcases hf x with ⟨y, rfl⟩,
  exact h y
end

#print rfl
#reduce exampl


#exit
import data.nat.gcd data.equiv.basic

#print equiv.set.univ

#exit
import data.set.basic data.fintype.basic data.equiv.encodable

variables {R A : Type} (P : R → A → bool)

def 𝕍_ (S : set R) : set A :=
{x : A | ∀ f ∈ S, P f x}

notation `𝕍`:max := 𝕍_ (by exact P)

def 𝕀_ (X : set A) : set R :=
{f : R | ∀ x ∈ X, P f x}

notation `𝕀`:max := 𝕀_ (by exact P)

set_option class.instance_max_depth 200

#eval let s := @fintype.choose (Σ' (P : finset (unit × unit)) (Y J : finset (unit)),
  (∀ (x : unit), (∀ (x_1 : unit), x_1 ∈ Y → ((x, x_1) ∈ P)) → x ∈ J) ∧ ¬
    ∀ (x : unit), (∀ (f : unit), f ∈ J → ((f, x) ∈ P)) → x ∈ Y) _ _ (λ _, true) _ sorry in
(s.1, s.2.1, s.2.2.1)

lemma Galois_connection : ¬
  ∀ (P : unit→ unit→ bool) {Y : finset (unit)} {J : finset (unit)},
  𝕀 (↑Y: set (unit)) ⊆ ↑J ↔ 𝕍 (↑J : set (unit)) ⊆ ↑Y :=
begin
  dsimp [𝕀_, 𝕍_, set.subset_def],
  simp,
  exact dec_trivial,

end

#exit
import order.filter.basic

#print filter.cofinite
open filter set
variables {α : Type*}
@[simp] lemma mem_cofinite {s : set α} : s ∈ (@cofinite α) ↔ finite (-s) := iff.rfl

example : @cofinite ℕ = at_top :=
begin
  ext s,
  simp only [mem_cofinite, mem_at_top_sets],



end

#exit
import data.mv_polynomial data.fintype

open polynomial

variables {R : Type*} {σ : Type*} [integral_domain R] [infinite R]

open_locale classical

lemma eval_eq_zero (f : polynomial R) : (∀ x, f.eval x = 0) ↔ f = 0 :=
⟨λ h, let ⟨x, hx⟩ := infinite.exists_not_mem_finset (roots f) in
  by_contradiction (mt mem_roots (λ hiff, hx (hiff.2 (h x)))),
by rintro rfl; simp⟩
#print mv_polynomial.comm_ring
lemma mv_polynomial.eval_eq_zero (f : mv_polynomial σ R) : (∀ x, f.eval x = 0) ↔ f = 0 :=
finsupp



#exit
import data.set.lattice
variables p q r : Prop
open set
example (R : Type*) (A : Type*) (P : R → A → Prop)
  (ι : Type*) (S : ι → set R) (x : A) :
(∀ (f : R), (f ∈ ⋃ (i : ι), S i) → P f x) ↔
  ∀ (i : ι) (f : R), f ∈ S i → P f x :=
begin
  simp, tauto,
end

theorem T2R : ((p ∨ q) → r) → (p → r) ∧ (q → r) :=
begin
    intros porqr,
    split,
    { assume hp : p,
      apply porqr,
      left,
      exact hp },
    { assume hq : q,
      apply porqr,
      right,
      exact hq },
end
noncomputable theory
open_locale classical

def foo : Π (X : Type), X → X :=
λ X, if h : X = ℕ then by {subst h; exact nat.succ } else id

example (claim : (Π X : Type, X → X) ≃ unit) : false :=
let foo : Π (X : Type), X → X :=
  λ X, if h : X = ℕ then by {subst h; exact nat.succ } else id in
by simpa [foo] using congr_fun (congr_fun (claim.injective
   (subsingleton.elim (claim @id) (claim foo))) ℕ) 0

#exit
import linear_algebra.basic

theorem Distr_or_L (p q r : Prop) : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) :=
begin
    intros pqpr,
    have porq : p ∨ q, from pqpr.left,
    have porr : p ∨ r, from pqpr.right,
    { cases porq with hp hq,
      { exact or.inl hp },
      { cases porr with hp hr,
        { exact or.inl hp },
        { exact or.inr ⟨hq, hr⟩ } } }
end
#print linear_map
example : Σ

#exit
import topology.compact_open topology.separation

open function

example {X Y : Type} [topological_space X] [topological_space Y] (f : X → Y) [compact_space X]
  [t2_space Y] (hf : continuous f) (hfs : surjective f) (U : set Y) (hU : is_open (f ⁻¹' U)) :
  is_open U :=
have h : is_closed (f '' (f⁻¹' -U)), from _,
begin



end

#exit
import data.rat.denumerable

#eval denumerable.equiv₂ ℕ ℚ 20

#eval denumerable.equiv₂ ℚ ℕ ((denumerable.equiv₂ ℕ ℚ 3) + (denumerable.equiv₂ ℕ ℚ 1))

#eval (denumerable.equiv₂ (Σ n : ℕ, fin n) ℕ) (8,3)

constant fintype (α : Type) : Type

attribute [class] fintype

def card (α : Type) [fintype α]: ℕ := sorry

constant fintype_subset {α : Type} [fintype α] {p : set α} : fintype ↥p

attribute [instance] fintype_subset

instance {α β : Type} [fintype β] (f : β → α) : fintype (set.range f) := sorry

lemma subset_lemma {α : Type} [fintype α] {p : set α} : card p = card p := sorry

example {α β : Type} [fintype α] [fintype β] (f : β → α) :
  card (set.range f) = card (set.range f):=
begin
  rw [subset_lemma], --fails
end

#exit

import data.setoid

def M : Type := (classical.choice ⟨sigma.mk ℕ nat.monoid⟩).1

noncomputable instance : monoid M := (classical.choice ⟨sigma.mk ℕ nat.monoid⟩).2

inductive monoid_expr (α : Type) : Type
| of (a : α) : monoid_expr
| one {} : monoid_expr
| mul    : monoid_expr → monoid_expr → monoid_expr

open monoid_expr

def eval {α β : Type} [has_mul β] [has_one β] (f : α → β) : monoid_expr α → β
| (of x) := f x
| one := 1
| (mul x y) := eval x * eval y

instance : setoid (monoid_expr M) :=
{ r := λ x y, eval id x = eval id y,
  iseqv := ⟨λ _, rfl, λ _ _, eq.symm, λ _ _ _, eq.trans⟩ }

def M' : Type := @quotient (monoid_expr M) monoid_expr.setoid

instance : monoid M' :=
{ mul := λ x y,
    quotient.lift_on₂' x y (λ x y, ⟦mul x y⟧)
      (λ a₁ a₂ b₁ b₂ (h₁ : _ = _) (h₂ : _ = _),
      quotient.sound $ show _ = _,
        by simp [eval, *]),
  mul_assoc := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quotient.sound (mul_assoc (eval id a) _ _)),
  one := ⟦one⟧,
  one_mul := λ a, quotient.induction_on a
    (λ a, quotient.sound (one_mul (eval id a))),
  mul_one := λ a, quotient.induction_on a
    (λ a, quotient.sound (mul_one (eval id a))) }

#exit
import data.fintype.basic tactic.fin_cases
variables p q : Prop

open classical

example : ¬(p → q) → p ∧ ¬q :=
λ h,
have notq : ¬q, from (λ hq', (h (λ hp, hq'))),
and.intro
(or.elim (em p)
id
(
(λ hnp, _)))
notq


instance decidable_eq_endofunctions {qq : Type} [fintype qq] [decidable_eq qq] :
  decidable_eq (qq → qq) := by apply_instance
inductive nand_expr (n : ℕ) : Type
| false {} : nand_expr
| var (i : fin n) : nand_expr
| nand : nand_expr → nand_expr → nand_expr

{x : A × B | ∃ a : A, X = (a, f a)}

namespace nand_expr

def eval {n : ℕ} : nand_expr n → (fin n → bool) → bool
| false      x := ff
| (var i)    x := x i
| (nand a b) x := !((eval a x) && (eval b x))

lemma surjective_eval : Π {n : ℕ} (f : (fin n → bool) → bool),
  {e : nand_expr n // e.eval = f }
| 0 := λ f, if hf : f fin.elim0 = ff
  then ⟨false, funext $ λ x, hf.symm.trans sorry⟩
  else ⟨nand false false, sorry⟩
| (n+1) := λ f, _

end nand_expr

#exit
import data.set.basic

inductive mynat
| zero : mynat
| succ : mynat → mynat

namespace mynat

def one : mynat := succ zero

def two : mynat := succ one

def add (a b : mynat) : mynat :=
mynat.rec b (λ _, succ) a

lemma one_add_one : add one one = two := eq.refl two

lemma one_add_one' : 1 + 1 = 2 := eq.refl 2

set_option pp.all true
#print one_add_one



set_option pp.all true

#print exampl

import system.io

def main : io nat :=
do io.put_str "Hello world", return 1

#exit
import tactic.ring data.complex.basic

example (a b c : ℂ) :
  (a + b + c)^2 + (a + b - c)^2 + (a + c - b)^2 + (b + c - a)^2 =
  (2 * a)^2 + (2 * b)^2 + (2 * c)^2 := by ring


#exit
import logic.basic data.fintype.basic tactic.tauto

def xo (a b : Prop) := ¬(a ↔ b)

lemma xo_assoc_aux1 (a b c : Prop) (h : xo (xo a b) c) : xo a (xo b c) :=
λ h₁,
have h : ¬(¬(¬(b ↔ c) ↔ b) ↔ c),
  from λ h₂,
    h ⟨λ hab, h₂.mp (λ h₃, hab (h₁.trans h₃)),
      λ hc hab, h₂.mpr hc (h₁.symm.trans hab)⟩,
have hnc : ¬ c,
  from λ hc, h ⟨λ _, hc, λ hc hbcb,
    have hnb : ¬ b, from λ hb, hbcb.mpr hb (iff_of_true hb hc),
    hnb (hbcb.mp (λ hbc, hnb (hbc.mpr hc)))⟩,
have h : ¬(¬(b ↔ c) ↔ b),
  from (not_not_not_iff _).1 (λ h₁, h ⟨λ h₂, (h₁ h₂).elim, λ hc, (hnc hc).elim⟩),
have h : ¬ (¬ ¬ b ↔ b),
  from λ hb,
    h ⟨λ h, hb.mp (λ hnb, h (iff_of_false hnb hnc)), λ hb hbc, hnc (hbc.mp hb)⟩,
have hnb : ¬ b,
  from λ hb, h (iff_of_true (λ hnb, hnb hb) hb),
h ⟨λ hnnb, (hnnb hnb).elim, λ hb, (hnb hb).elim⟩
#reduce xo_assoc_aux1
lemma xo_assoc_aux2 (a b c : Prop) : xo (xo a b) c → xo a (xo b c) :=
begin
  dsimp [xo],
  assume h h₁,
  replace h : ¬(¬(¬(b ↔ c) ↔ b) ↔ c),
  { assume h₂,
    apply h,
    split,
    { assume hab : ¬ (a ↔ b),
      apply h₂.mp,
      assume h₃,
      apply hab,
      apply h₁.trans,
      exact h₃ },
    { assume hc : c,
      assume hab : a ↔ b,
      apply h₂.mpr hc,
      apply h₁.symm.trans,
      exact hab } },
  clear h₁ a,
  have hnc : ¬ c,
  { assume hc : c,
    apply h,
    split,
    { exact λ _, hc },
    { assume hc hbcb,
      have hnb : ¬ b,
      { assume hb : b,
        apply hbcb.mpr hb,
        exact iff_of_true hb hc },
      { apply hnb,
        apply hbcb.mp,
        assume hbc,
        apply hnb,
        apply hbc.mpr,
        exact hc } } },
  replace h : ¬(¬¬(¬(b ↔ c) ↔ b)),
  { assume h₁,
    apply h,
    split,
    { assume h₂,
      exact (h₁ h₂).elim },
    { assume hc, exact (hnc hc).elim } },
  replace h := (not_not_not_iff _).1 h,
  replace h : ¬ (¬ ¬ b ↔ b),
  { assume hb,
    apply h,
    split,
    { assume h,
      apply hb.mp,
      assume hnb,
      apply h,
      exact iff_of_false hnb hnc },
    { assume hb hbc,
      apply hnc,
      apply hbc.mp hb } },
  clear hnc c,
  have hnb : ¬ b,
  { assume hb,
    apply h,
    exact iff_of_true (λ hnb, hnb hb) hb },
  apply h,
  exact ⟨λ hnnb, (hnnb hnb).elim, λ hb, (hnb hb).elim⟩
end

#reduce xo_assoc_aux


#print ring
set_option class.instance_max_depth 200
instance : fintype (ring bool) :=
fintype.of_equiv
  (Σ' (add : bool → bool → bool)
      (add_assoc : ∀ a b c, add (add a b) c = add a (add b c))
      (zero : bool)
      (zero_add : ∀ a, add zero a = a)
      (add_zero : ∀ a, add a zero = a)
      (neg : bool → bool)
      (add_left_neg : ∀ a, add (neg a) a = zero)
      (add_comm : ∀ a b, add a b = add b a)
      (mul : bool → bool → bool)
      (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c))
      (one : bool)
      (one_mul : ∀ a, mul one a = a)
      (mul_one : ∀ a, mul a one = a)
      (left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)),
      ∀ b c a, mul (add b c) a = add (mul b a) (mul c a) )
  { to_fun := λ ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩,
      ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩,
    inv_fun := λ ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩,
      ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩,
    left_inv := λ ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩, rfl,
    right_inv := λ a, by cases a; refl }

#eval fintype.card {op : bool → bool → bool //
  ∀ a b c, op (op a b) c = op a (op b c)}

example : fintype.card (ring bool) = 2 := rfl


local attribute [instance, priority 0] classical.prop_decidable

lemma iff.assoc {a b c : Prop} : ((a ↔ b) ↔ c) ↔ (a ↔ (b ↔ c)) :=
if h : a then by simp [h] else by simp [h, not_iff]

lemma or_iff_distrib_left {a b c : Prop} : (a ∨ (b ↔ c)) ↔ ((a ∨ b) ↔ (a ∨ c)) :=
⟨λ h, by cases h; simp [h], λ h, by by_cases a; simp * at *⟩

lemma or_iff_distrib_right {a b c : Prop} : ((a ↔ b) ∨ c) ↔ ((a ∨ c) ↔ (b ∨ c)) :=
by rw [or_comm, or_iff_distrib_left, or_comm, or_comm c]

instance : discrete_field Prop :=
{ add := (↔),
  mul := (∨),
  add_assoc := λ _ _ _, propext $ iff.assoc,
  zero := true,
  zero_add := λ _, propext $ true_iff _,
  add_zero := λ _, propext $ iff_true _,
  neg := id,
  add_left_neg := λ _, propext $ iff_true_intro iff.rfl,
  add_comm := λ _ _, propext iff.comm,
  mul_assoc := λ _ _ _, propext $ or.assoc,
  one := false,
  one_mul := λ _, propext $ false_or _,
  mul_one := λ _, propext $ or_false _,
  left_distrib := λ _ _ _, propext $ or_iff_distrib_left,
  right_distrib := λ _ _ _, propext $ or_iff_distrib_right,
  mul_comm := λ _ _, propext $ or.comm,
  inv := id,
  zero_ne_one := true_ne_false,
  mul_inv_cancel := λ a ha0, if ha : a
    then (ha0 (eq_true_intro ha)).elim
    else eq_false_intro (λ h, h.elim ha ha),
  inv_mul_cancel := λ a ha0, if ha : a
    then (ha0 (eq_true_intro ha)).elim
    else eq_false_intro (λ h, h.elim ha ha),
  has_decidable_eq := classical.dec_eq _,
  inv_zero := rfl }


variable V : Type

structure toto := (val : list V)

inductive shorter : toto V -> toto V -> Prop
| step : ∀ (z : V) (l : list V), shorter ⟨l⟩ ⟨z::l⟩

lemma shorter_wf : well_founded (shorter V)
    := by { apply well_founded.intro, intro l, cases l with xs,
        induction xs with y ys; apply acc.intro; intros; cases a,
        apply xs_ih }

instance : has_well_founded (toto V) := ⟨shorter V, shorter_wf V⟩
#print int.comm_semiring
def fold : toto V -> Prop
    | ⟨[]⟩    := true
    | ⟨x::xs⟩ := have h : shorter V ⟨xs⟩ ⟨x::xs⟩ := shorter.step x xs,
        fold ⟨xs⟩
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, shorter_wf V⟩],
  dec_tac := `[exact h] }

#exit
import set_theory.ordinal

universe u
noncomputable theory
#print axioms int.comm_ring
example : ((<) : cardinal.{u} → cardinal.{u} → Prop)
  ≼o ((<) : ordinal.{u} → ordinal.{u} → Prop) :=
cardinal.ord.order_embedding

def ordinal.to_cardinal : ordinal.{u} → cardinal.{u}
| o := begin
  have :=


end


example : ((<) : ordinal.{u} → ordinal.{u} → Prop)
  ≼o ((<) : cardinal.{u} → cardinal.{u} → Prop) :=
⟨⟨λ o : ordinal.{u}, well_founded.fix ordinal.wf.{u} begin end o, _⟩, _⟩

#exit
import linear_algebra.basic

set_option pp.implicit true




lemma X {p q : Prop} : (p ↔ ¬q) ↔ ¬(p ↔ q) :=
sorry
#print not_false
example {p : Prop} : p ∨ ¬p :=
((@X (p ∨ ¬p) false).mpr (λ h, h.mp (or.inr (λ hp, h.mp (or.inl hp))))).mpr (λb,b)

example := by library_search

example {α : Type} (s : set α) : s = s ⁻¹' {true} :=
set.ext $ λ x, ⟨λ h, or.inl (eq_true_intro h),
  λ h, h.elim (λ h, h.mpr trivial) false.elim⟩

example {ι : Type} (i : ι) (f : Π (j : subtype (≠ i)), M₁ j.val)

import topology.opens

open topological_space

lemma opens.supr_val {X γ : Type*} [topological_space X] (ι : γ → opens X) :
  (⨆ i, ι i).val = ⨆ i, (ι i).val :=
@galois_connection.l_supr (opens X) (set X) _ _ _ (subtype.val : opens X → set X)
    opens.interior opens.gc _

lemma what_is_this_called {X Y : Type*} [topological_space X] [topological_space Y] {f : X → Y}
  (hf : continuous f) {γ : Type*} (ι : γ → opens Y) :
  (⨆ (j : γ), hf.comap (ι j)).val = ⋃ (j : γ), f ⁻¹' (ι j).val :=
opens.supr_val _

#exit
import algebra.pi_instances

universes u v w

class SemiModule (β : Type v) [add_comm_monoid β]

abbreviation Module (β : Type v) [add_comm_group β] :=
SemiModule β

instance piSemiModule (I : Type w) (f : I → Type u)
  [∀ i, add_comm_monoid $ f i] [∀ i, SemiModule (f i)] :
  SemiModule (Π i : I, f i) := by constructor
set_option pp.implicit true
-- instance piSemiModule' (I : Type w) (f : I → Type u)
--   [∀ i, add_comm_group $ f i] [∀ i, SemiModule (f i)] :
--   SemiModule (Π i : I, f i) := begin

--     apply_instance

--   end

example (I : Type w) (f : I → Type u) [∀ i, add_comm_group $ f i] :
  @pi.add_comm_monoid I f _ = @add_comm_group.to_add_comm_monoid _ _ := rfl
set_option trace.class_instances true
#check piSemiModule _ _
instance piModule (I : Type w) (f : I → Type u)
  [∀ i, add_comm_group $ f i] [∀ i, SemiModule (f i)] : -- changed from Module
  Module (Π i : I, f i) := begin
  delta Module,
  -- ⊢ SemiModule (Π (i : I), f i)
  -- apply piSemiModule I f, -- works
  apply_instance -- still fails
end
/-
@SemiModule (Π (i : I), f i)
  (@pi.add_comm_monoid I (λ (i : I), f i) (λ (i : I), _inst_1 i))

-/
#exit
import ring_theory.integral_closure set_theory.schroeder_bernstein
#print function.embedding.trans
example {R A : Type} [comm_ring A] [comm_ring R] [algebra R A] (S : subalgebra R A)
  {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S := by library_search
open_locale classical
example {α β ι : Type*} [hι : nonempty ι] {S : ι → set α} (f : α → β)
  (hf : function.injective f) : (⨅ i, f '' S i) = f '' (⨅ i, S i) :=
by resetI; rcases hι with ⟨i⟩; exact
  set.ext (λ x, ⟨λ h, by rcases set.mem_Inter.1 h i with ⟨y, hy, rfl⟩;
    exact ⟨y, set.mem_Inter.2 (λ j, by rcases set.mem_Inter.1 h j with ⟨z, hz⟩;
      exact (hf hz.2 ▸ hz.1)), rfl⟩,
  by rintros ⟨y, hy, rfl⟩; exact set.mem_Inter.2 (λ i, set.mem_image_of_mem _
    (set.mem_Inter.1 hy _))⟩)
/-
structure functor (C : Type u₁) [category.{v₁} C] (D : Type u₂) [category.{v₂} D] :
  Type (max v₁ v₂ u₁ u₂) :=
(obj       : C → D)
(map       : Π {X Y : C}, (X ⟶ Y) → ((obj X) ⟶ (obj Y)))
(map_id'   : ∀ (X : C), map (𝟙 X) = 𝟙 (obj X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

infixr ` ⥤ `:26 := functor       -- type as \func --
-/

variables {X : Type*} [topological_space X]

open topological_space

def res_functor {Y₁ Y₂ : set X} (hY : Y₂ ⊆ Y₁) :
    {V : opens X // Y₁ ⊆ V} ⥤ {V : opens X // Y₂ ⊆ V} :=
{ obj := λ V, ⟨V.1, set.subset.trans hY V.2⟩,
  map := λ _ _, id}

example (Y : set X) : res_functor (set.subset.refl Y) = 𝟭 _ :=
begin
  apply category_theory.functor.mk.inj_eq.mpr,
  simp, refl,
end

#exit
import data.nat.prime data.zsqrtd.gaussian_int

inductive W {α : Type*} (β : α → Type*)
| mk (a : α) (b : β a → W) : W

def blah {α : Type*} (β : α → Type*) [Π a, fintype (β a)] : W β → ℕ
| mk a b := begin


end



local notation `ℤ[i]` := gaussian_int
#eval let s := (finset.Ico 20 10000).filter nat.prime in
  ((s.sigma (λ n, (finset.Ico 20 n).filter nat.prime)).filter
  (λ n : Σ n, ℕ, nat.sqrt (n.1^2 - n.2^2) ^ 2 = n.1^2 - n.2^2)).image
  (λ n : Σ n, ℕ, (n.1, n.2, (n.1^2 - n.2^2).factors))
#eval nat.factors (71^2 + 31^2)
#eval (nat.prime 31 : bool)
#eval nat.sqrt(181^2 - 19^2)
#eval nat.factors 180
#eval (180^2 + 19^2 = 181^2 : bool)
#eval (nat.prime 181 : bool)

import tactic.split_ifs

open nat

inductive tree : Type
| lf : tree
| nd : tree -> nat -> tree -> tree

open tree

def fusion : tree -> tree -> tree
| lf t2 := t2
| (nd l1 x1 r1) lf := (nd l1 x1 r1)
| (nd l1 x1 r1) (nd l2 x2 r2) :=
    if x1 <= x2
    then nd (fusion r1 (nd l2 x2 r2)) x1 l1
    else nd (fusion (nd l1 x1 r1) r2) x2 l2

def occ : nat -> tree -> nat
| _ lf := 0
| y (nd g x d) := (occ y g) + (occ y d) + (if x = y then 1 else 0)

theorem q5 : ∀ (x : ℕ) (t1 t2 : tree),
    (occ x (fusion t1 t2)) = (occ x t1) + (occ x t2) :=
begin
    intros x t1 t2,
    induction t1 with g1 x1 d1 _ ih1,
    simp [fusion, occ],
    induction t2 with g2 x2 d2 _ ih2,
    simp [fusion, occ],
    by_cases x1 <= x2,
    simp [fusion, h, occ],
    rw ih1,
    simp [occ, fusion, h],
    simp [occ, fusion, h],
    rw ih2,
    simp [occ, fusion],
end
∀ t2
theorem q5 : ∀ (x : ℕ) (t1 t2 : tree),
    (occ x (fusion t1 t2)) = (occ x t1) + (occ x t2) :=
begin
  intros x t1,
  induction t1 with g1 x1 d1 _ ih1,
  { simp [fusion, occ] },
  { assume t2,
    induction t2 with g2 x2 d2 _ ih2,
    simp [fusion, occ],
    by_cases x1 <= x2,
    { simp [fusion, h, occ, ih1] },
    { simp [occ, fusion, h, ih2] }, },
end

theorem q5 (x : ℕ) : ∀ (t1 t2 : tree),
    (occ x (fusion t1 t2)) = (occ x t1) + (occ x t2)
| lf t2 := by simp [fusion, occ]
| (nd l1 x1 r1) lf := by simp [fusion, occ]
| (nd l1 x1 r1) (nd l2 x2 r2) :=
begin
  simp only [fusion, occ],
  by_cases hx12 : x1 ≤ x2,
  { rw [if_pos hx12],
    simp only [fusion, occ],
    rw q5,
    simp [occ] },
  { rw if_neg hx12,
    simp only [fusion, occ],
    rw q5,
    simp [occ] }
end


#exit
import ring_theory.algebra

example {R : Type*} [comm_ring R] :
  (algebra.to_module : module ℤ R) = add_comm_group.module :=


variable {n : ℕ}
open function nat finset
#print test_bit
def binary (A : finset ℕ) : ℕ := A.sum (λ x, pow 2 x)

def ith_bit (n i : ℕ) := n / 2 ^ i % 2


-- lemma ith_bit_binary (A : finset ℕ) : ∀ i,
--   i ∈ A ↔ ¬ even (binary A / 2 ^ i) :=
-- finset.induction_on A
--   (by simp [binary, ith_bit])
--   (λ a s has ih i,
--     begin
--       dsimp [binary, ith_bit] at *,
--       rw [sum_insert has, mem_insert],
--       have hnm : ∀ {n m}, n < m → 2^n / 2^m = 0,
--         from λ n m h, div_eq_of_lt ((pow_lt_iff_lt_right (le_refl _)).2 h),
--       have hnm' : ∀ {n m : ℕ}, n < m → 2^m % 2^n = 0, from sorry,
--       have h2p : ∀ {n : ℕ}, 0 < 2^n, from sorry,
--       rcases lt_trichotomy i a with hia|rfl|hai,
--       { have : even (2^a / 2^i),
--         { rw [even_div, mod_mul_left_div_self, ← dvd_iff_mod_eq_zero],
--           apply dvd_div_of_mul_dvd,
--           rw [← nat.pow_succ],
--           exact pow_dvd_pow _ hia }, sorry,
--         -- rw [hnm' hia, zero_add, if_neg (not_le_of_gt (mod_lt _ h2p))],
--         -- simp [*, ne_of_lt hia, ih, hnm' hia] with parity_simps
--          }, { sorry },
--       -- { rw [mod_self, zero_add, if_neg (not_le_of_gt (mod_lt _ h2p))],
--       --   simp [nat.div_self (nat.pow_pos h2p _), nat.mod_self] with parity_simps,
--       --   finish },--finish },
--       {
--         -- have : 2 ^ a + sum s (pow 2) % 2 ^ i = (2 ^ a + sum s (pow 2)) % 2 ^ i,
--         --   from begin
--         --     rw [add_mod]

--         --   end,
--         -- rw [hnm hai, mod_eq_of_lt ((pow_lt_iff_lt_right (le_refl _)).2 hai)],
--         rw [even_div],
--         simp [ne_of_gt hai, hnm hai, ih] with parity_simps, },
--     end)

lemma ith_bit_binary (A : finset ℕ) : ∀ i,
  i ∈ A ↔ ¬ even (binary A / 2 ^ i) :=
finset.induction_on A
  (by simp [binary, ith_bit])
  (λ a s has ih i,
    begin
      dsimp [binary, ith_bit] at *,
      rw [sum_insert has, mem_insert,
        nat.add_div (nat.pow_pos (show 0 < 2, from dec_trivial) _)],
      have hnm : ∀ {n m}, n < m → 2^n / 2^m = 0,
        from λ n m h, div_eq_of_lt ((pow_lt_iff_lt_right (le_refl _)).2 h),
      have hnm' : ∀ {n m : ℕ}, n < m → 2^m % 2^n = 0, from sorry,
      have h2p : ∀ {n : ℕ}, 0 < 2^n, from sorry,
      rcases lt_trichotomy i a with hia|rfl|hai,
      { have : even (2^a / 2^i),
        { rw [even_div, mod_mul_left_div_self, ← dvd_iff_mod_eq_zero],
          apply dvd_div_of_mul_dvd,
          rw [← nat.pow_succ],
          exact pow_dvd_pow _ hia },
        rw [hnm' hia, zero_add, if_neg (not_le_of_gt (mod_lt _ h2p))],
        simp [*, ne_of_lt hia, ih, hnm' hia] with parity_simps },
      { rw [mod_self, zero_add, if_neg (not_le_of_gt (mod_lt _ h2p))],
        simp [nat.div_self (nat.pow_pos h2p _), nat.mod_self] with parity_simps,
        finish },--finish },
      { have : (2 ^ a + sum s (pow 2)) % 2 ^ i < 2 ^ a + sum s (pow 2) % 2 ^ i,
          from _,
        rw [hnm hai, mod_eq_of_lt ((pow_lt_iff_lt_right (le_refl _)).2 hai)],

        simp [ne_of_gt hai, hnm hai, ih] with parity_simps, },
    end)

lemma ith_bit_binary (A : finset ℕ) : ∀ i,
  i ∈ A ↔ ith_bit (binary A) i = 1 :=
finset.induction_on A
  (by simp [binary, ith_bit])
  (λ a s has ih i, begin
    dsimp [binary, ith_bit] at *,
    rw [sum_insert has, mem_insert, nat.add_div],
    rcases lt_trichotomy i a with hia|rfl|hai,
    {
      rw [if_neg, add_zero],
       }






  end)

example : function.injective (binary) :=
function.injective_of_has_left_inverse
  ⟨λ n, (range n).filter (λ i, n / 2^i ≠ n / 2^(i+1)),
  λ s, finset.induction_on s
    (by simp [binary]) $
    λ a s has ih, begin
      conv_rhs { rw ← ih },
      ext i,
      simp only [binary, sum_insert has, mem_filter, mem_range,
        mem_insert],
      split,
      { assume h,
         }



    end⟩
-- λ s, finset.induction_on s
--   (λ t h, begin simp [binary] at *, end) $
-- λ a s has ih t h,
-- have hat : binary t = binary (insert a (t.erase a)),
--   from h ▸ congr_arg binary (by finish [finset.ext]),
-- begin
--   rw [erase_in]


-- end

example (m : nat) : 0 * m = 0 :=
begin
  induction m with m ih,
  rw mul_zero,
  rw [nat.mul_succ],


end

lemma z (a b c : ℝ) : a^3 + b^3 + c^3 - 3 * a * b * c =
  1/2 * (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2) := by ring

#print z

#exit
import data.set.basic


example {X : Type} (A B : set X) : A ∩ B = A ∪ B ↔ A = B :=
⟨λ h, set.ext $ λ x,
  ⟨λ hA, set.mem_of_subset_of_mem (set.inter_subset_right A B) (h.symm ▸ or.inl hA),
   λ hB, set.mem_of_subset_of_mem (set.inter_subset_left A B) (h.symm ▸ or.inr hB)⟩,
  by simp {contextual := tt}⟩

#exit
import data.int.basic

#print nat_abs
inductive cool : ℕ → Prop
| cool_2 : cool 2
| cool_5 : cool 5
| cool_sum : ∀ (x y : ℕ), cool x → cool y → cool (x + y)
| cool_prod : ∀ (x y : ℕ), cool x → cool y → cool (x*y)

example : 7 = sorry :=
begin
  dsimp only [bit0, bit1],

end

example : cool 7 := (cool.cool_sum 2 5 cool.cool_2 cool.cool_5 : _)

#exit
import data.polynomial

variables {R : Type*} [comm_ring R]
open polynomial

lemma zzzz {u r : R} {n : ℕ} (hr : r^n = 0) (hu : is_unit u) : is_unit (u + r) :=
have hnegr : (-r)^n = 0, by rw [neg_eq_neg_one_mul, mul_pow, hr, mul_zero],
have (X - C (-r)) ∣ X ^ n, from dvd_iff_is_root.2 (by simp [is_root, hnegr]),
is_unit_of_dvd_unit
  (let ⟨p, hp⟩ := this in ⟨p.eval u, by simpa using congr_arg (eval u) hp⟩)
  (is_unit_pow n hu)

#print acc.intro

#exit
import data.zmod.quadratic_reciprocity

@[simp] lemma list.lex_nil_right (l)

#eval @nat.modeq.chinese_remainder 5 8 rfl 4 7

#eval zmodp.legendre_sym 10 71 (by norm_num)

#eval zmodp.legendre_sym 2 71 (by norm_num)

#eval zmodp.legendre_sym 5 71 (by norm_num)

#eval zmodp.legendre_sym 71 5 (by norm_num)

example {α : Type} [nonempty α] (F G : α → Prop)
  (h : (∃ x, F x) → ∃ x, G x) : ∃ x, F x → G x :=
begin
  resetI,
  classical,
  cases _inst_1 with a,
  rcases classical.em (∃ x, G x) with ⟨x, hx⟩ | hx,
  { exact ⟨x, λ _, hx⟩ },
  { exact ⟨a, λ hF, (not_exists.1 (not_imp_not.2 h hx) a hF).elim ⟩ }
end


def sum' (f : ℕ → ℕ) : ℕ → ℕ
| 0     := 0
| (n+1) := sum' n + f n



#exit
import data.equiv.basic group_theory.perm.sign
#eval nat.choose 8 3
#eval (finset.range (721)).filter (λ x, x ∣ 720 ∧ x % 7 = 1)
#eval ((finset.Ico 1 31).powerset.filter
  (λ s : finset ℕ, s.card = 8 ∧
    ((s.filter (λ s : finset ℕ, s.card = 4)).1.map
    (λ s : finset ℕ, s.1.sum)).nodup)


open equiv equiv.perm
variable {α : Type}

open_locale classical

example (f : perm α) (a b : α) :
  f * swap a b * f⁻¹ = sorry :=
begin
  rw [mul_assoc, swap_mul_eq_mul_swap, inv_inv],
  simp,
end

#exit
inductive tree : Type
| lf : tree
| nd : tree -> nat -> tree -> tree

open tree

def fusion : tree -> tree -> tree
| lf t2 := t2
| t1 lf := t1
| (nd l1 x1 r1) (nd l2 x2 r2) :=
    if x1 ≤ x2
    then nd (fusion r1 (nd l2 x2 r2)) x1 l1
    else nd (fusion (nd l1 x1 r1) r2) x2 l2
-- using_well_founded { rel_tac := λ _ _,
--     `[exact ⟨_, measure_wf (λ t, tree.sizeof t.1 + tree.sizeof t.2)⟩] }

#print fusion._main._pack.equations._eqn_1

theorem fusion_lf : ∀ (t : tree), fusion lf lf = lf :=
λ _, rfl

example  (t : tree) : fusion t lf = lf :=
by cases t; refl
#exit
import data.real.nnreal

#print xor

example : (∀ p q r, xor (xor p q) r ↔ xor p (xor q r)) → ∀ p, p ∨ ¬p :=
λ h p,
((h p p true).1
    (or.inr ⟨trivial, λ h, h.elim (λ h, h.2 h.1) (λ h, h.2 h.1)⟩)).elim
  (λ h, or.inl h.1)
  (λ h, or.inr h.2)

example : (∀ p q, xor p q ↔ (p ∨ q) ∧ ¬(p ∧ q)) :=
λ p q, ⟨λ h, h.elim (λ h, ⟨or.inl h.1, λ h1, h.2 h1.2⟩)
    (λ h, ⟨or.inr h.1, λ h1, h.2 h1.1⟩),
  (λ h, h.1.elim
    (λ hp, or.inl ⟨hp, λ hq, h.2 ⟨hp, hq⟩⟩)
    (λ hq, or.inr ⟨hq, λ hp, h.2 ⟨hp, hq⟩⟩))⟩

example : (∀ p q r, ((p ↔ q) ↔ r) ↔ (p ↔ (q ↔ r))) → ∀ p, p ∨ ¬p :=
λ h p,
  ((h (p ∨ ¬p) false false).1
      ⟨λ h, h.1 (or.inr (λ hp, h.1 (or.inl hp))), false.elim⟩).2
    iff.rfl

inductive pre_free_group (α : Type) : Type
| atom : α → pre_free_group
| one : pre_free_group
| mul : pre_free_group → pre_free_group → pre_free_group
| inv : pre_free_group → pre_free_group

namespace pre_free_group

variable {α : Type}

instance : has_one (pre_free_group α) := ⟨pre_free_group.one _⟩
instance : has_mul (pre_free_group α) := ⟨pre_free_group.mul⟩
instance : has_inv (pre_free_group α) := ⟨pre_free_group.inv⟩

lemma mul_def : (*) = @pre_free_group.mul α := rfl
lemma one_def : 1 = @pre_free_group.one α := rfl
lemma inv_def : has_inv.inv = @pre_free_group.inv α := rfl

inductive rel : Π (a b : pre_free_group α), Prop
| mul_assoc : ∀ a b c, rel ((a * b) * c) (a * (b * c))
| one_mul : ∀ a, rel (1 * a) a
| mul_one : ∀ a, rel (a * 1) a
| mul_left_inv : ∀ a, rel (a⁻¹ * a) 1
| mul_lift : ∀ a b c d, rel a b → rel c d → rel (a * c) (b * d)
| inv_lift : ∀ a b, rel a b → rel (a⁻¹) (b⁻¹)
| refl : ∀ a, rel a a
| symm : ∀ a b, rel a b → rel b a
| trans : ∀ a b c, rel a b → rel b c → rel a c

instance (α : Type) : setoid (pre_free_group α) :=
{ r := rel,
  iseqv := ⟨rel.refl, rel.symm, rel.trans⟩ }

end pre_free_group

def free_group (α : Type) := quotient (pre_free_group.setoid α)

namespace free_group
open pre_free_group

variable {α : Type}

instance : group (free_group α) :=
{ one := ⟦1⟧,
  mul := λ a b, quotient.lift_on₂ a b (λ a b, ⟦a * b⟧)
    (λ a b c d h₁ h₂, quotient.sound (rel.mul_lift _ _ _ _ h₁ h₂)),
  inv := λ a, quotient.lift_on a (λ a, ⟦a⁻¹⟧)
    (λ a b h, quotient.sound (rel.inv_lift _ _ h)),
  mul_assoc := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quotient.sound (rel.mul_assoc _ _ _)),
  one_mul := λ a, quotient.induction_on a
    (λ a, quotient.sound (rel.one_mul a)),
  mul_one := λ a, quotient.induction_on a
    (λ a, quotient.sound (rel.mul_one a)),
  mul_left_inv := λ a, quotient.induction_on a
    (λ a, quotient.sound (rel.mul_left_inv _)) }

def atom (a : α) : free_group α := ⟦pre_free_group.atom a⟧

variables {G : Type} [group G]

def lift (G : Type) [group G] (f : α → G) : free_group α →* G :=
{ to_fun := λ a, quotient.lift_on a
    (λ a, show G, from pre_free_group.rec_on a f 1 (λ _ _, (*)) (λ _ g, g⁻¹))
    (λ a b h, begin
      dsimp,
      induction h;
      try { dsimp [mul_def, inv_def, one_def] };
      simp [mul_assoc, *] at *,
    end),
  map_one' := rfl,
  map_mul' := λ a b, quotient.induction_on₂ a b (λ _ _, rfl) }

lemma one_def : (1 : free_group α) = ⟦pre_free_group.one α⟧ := rfl
lemma mul_def {a b : pre_free_group α} :
  @eq (free_group α) ⟦pre_free_group.mul a b⟧ (⟦a⟧ * ⟦b⟧) := rfl
lemma inv_def {a : pre_free_group α} :
  @eq (free_group α) ⟦pre_free_group.inv a⟧ (⟦a⟧⁻¹) := rfl

@[simp] lemma mk_apply {α β : Type*} [monoid α] [monoid β] (f : α → β) (h₁ h₂) (a : α) :
  monoid_hom.mk f h₁ h₂ a = f a := rfl

@[simp] lemma lift_atom (f : α → G) (a : α) : lift G f (atom a) = f a := rfl

lemma lift_unique (f : α → G) (φ : free_group α →* G) (h : ∀ a, φ (atom a) = f a)
  (g : free_group α) : φ g = lift G f g :=
quotient.induction_on g
  (λ a, begin
    dsimp [atom, lift] at *,
    induction a;
    simp [*, one_def.symm, mul_def, inv_def] at *;
    refl,
  end)

end free_group

#exit
import algebra.free

universe u

inductive pre_free_ring (α : Type u) : Type u
| atom : α → pre_free_ring
| zero : pre_free_ring
| one : pre_free_ring
| neg : pre_free_ring → pre_free_ring
| mul : pre_free_ring → pre_free_ring → pre_free_ring
| add : pre_free_ring → pre_free_ring → pre_free_ring

namespace pre_free_ring

variable {α : Type u}

instance : has_zero (pre_free_ring α) := ⟨pre_free_ring.zero _⟩
instance : has_one (pre_free_ring α) := ⟨pre_free_ring.one _⟩
instance : has_neg (pre_free_ring α) := ⟨pre_free_ring.neg⟩
instance : has_mul (pre_free_ring α) := ⟨pre_free_ring.mul⟩
instance : has_add (pre_free_ring α) := ⟨pre_free_ring.add⟩

inductive rel : Π (a b : pre_free_ring α), Prop
| add_assoc : ∀ a b c, rel (a + b + c) (a + (b + c))
| zero_add : ∀ a, rel (0 + a) a
| add_zero : ∀ a, rel (a + 0) a
| add_left_neg : ∀ a, rel (-a + a) 0
| add_comm : ∀ a b, rel (a + b) (b + a)
| mul_assoc : ∀ a b c, rel (a * b * c) (a * (b * c))
| one_mul : ∀ a, rel (1 * a) a
| mul_one : ∀ a, rel (a * 1) a
| left_distrib : ∀ a b c, rel (a * (b + c)) (a * b + a * c)
| right_distrib : ∀ a b c, rel ((a + b) * c) (a * c + b * c)
| add_lift : ∀ a b c d, rel a b → rel c d → rel (a + c) (b + d)
| mul_lift : ∀ a b c d, rel a b → rel c d → rel (a * c) (b * d)
| neg_lift : ∀ a b, rel a b → rel (-a) (-b)
| refl : ∀ a, rel a a
| symm : ∀ a b, rel a b → rel b a
| trans : ∀ a b c, rel a b → rel b c → rel a c

instance (α : Type u) : setoid (pre_free_ring α) :=
{ r := rel,
  iseqv := ⟨rel.refl, rel.symm, rel.trans⟩ }

end pre_free_ring

variable {α : Type u}

def free_ring (α : Type u) := quotient (pre_free_ring.setoid α)

namespace free_ring

open pre_free_ring

instance : ring (free_ring α) :=
{ zero := quotient.mk' 0,
  one := quotient.mk' 1,
  add := λ a b, quotient.lift_on₂ a b (λ a b, quotient.mk (a + b))
    (λ a b c d h₁ h₂, quot.sound (rel.add_lift _ _ _ _ h₁ h₂)),
  mul := λ a b, quotient.lift_on₂ a b (λ a b, quotient.mk (a * b))
    (λ a b c d h₁ h₂, quot.sound (rel.mul_lift _ _ _ _ h₁ h₂)),
  add_assoc := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quot.sound (rel.add_assoc _ _ _)),
  mul_assoc := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quot.sound (rel.mul_assoc _ _ _)),
  zero_add := λ a, quotient.induction_on a (λ a, quot.sound (rel.zero_add a)),
  add_zero := λ a, quotient.induction_on a (λ a, quot.sound (rel.add_zero a)),
  neg := λ a, quotient.lift_on a (λ a, quotient.mk (-a))
    (λ a b h, quot.sound (rel.neg_lift _ _ h)),
  add_left_neg := λ a, quotient.induction_on a
    (λ a, quot.sound (rel.add_left_neg _)),
  add_comm := λ a b, quotient.induction_on₂ a b
    (λ a b, quotient.sound (rel.add_comm _ _)),
  one_mul := λ a, quotient.induction_on a (λ a, quot.sound (rel.one_mul a)),
  mul_one := λ a, quotient.induction_on a (λ a, quot.sound (rel.mul_one a)),
  left_distrib := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quot.sound (rel.left_distrib _ _ _)),
  right_distrib := λ a b c, quotient.induction_on₃ a b c
    (λ a b c, quot.sound (rel.right_distrib _ _ _)) }

def atom : α → free_ring α := λ a, ⟦atom a⟧

#print linear_ordered_ring
#print
inductive le : free_ring bool → free_ring bool → Prop
| atom : le (atom ff) (atom tt)
| refl : ∀ x, le x x
| trans : ∀ a b c, le a b → le b c → le a c
| add_le_add_left :


#exit
import group_theory.subgroup algebra.commute

lemma X {α : Type} {φ : α → Prop}: (¬ ∃ v, φ v) ↔ (∀ v, ¬ φ v) :=
⟨λ ex v hv, ex ⟨v, hv⟩, Exists.rec⟩

#exit

open equiv
variables {G : Type*} [group G]
#print equiv.ext
def L (g : G) : perm G := ⟨λ h, g * h, λ h, g⁻¹ * h, λ _, by simp, λ _, by simp⟩

def R (g : G) : perm G := ⟨λ h, h * g⁻¹, λ h, h * g, λ _, by simp, λ _, by simp⟩

lemma perm.ext_iff {f g : perm G} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, by rw h, equiv.perm.ext _ _⟩

lemma forall_mem_range {α β : Type*} {p : β → Prop} {f : α → β} :
  (∀ x ∈ set.range f, p x) ↔ (∀ x, p (f x)) :=
⟨λ h x, h _ (set.mem_range_self _), by rintros h x ⟨y, rfl⟩; exact h _⟩

lemma question_4 : set.centralizer (set.range L : set (perm G)) = set.range R :=
calc set.centralizer (set.range L) = { σ  : perm G | ∀ g g₁, σ (g * g₁) = g * σ g₁ } :
  by simp only [set.ext_iff, commute, semiconj_by, set.centralizer, forall_mem_range, perm.ext_iff];
    tauto
... = set.range R : set.ext $ λ f,
  ⟨λ h, ⟨(f 1)⁻¹, perm.ext_iff.2 $ λ x, by dsimp [R]; rw [inv_inv, ← h, mul_one]⟩,
    by rintros ⟨g, rfl⟩; simp [R, mul_assoc]⟩

#print Z
-- set.subset.antisymm
--   (λ f h, ⟨(f 1)⁻¹, perm.ext_iff.2 $ λ x, begin
--     have := h (L (f 1)) (set.mem_range_self _) ,
--     simp [commute, semiconj_by, L, R, perm.ext_iff] at *,


--   end⟩ )
  -- (λ f, by rintros ⟨g, rfl⟩ f ⟨h, rfl⟩;
  --   simp [set.centralizer, L, R, perm.ext_iff, commute, semiconj_by, mul_assoc])



instance : is_subgroup

#exit
import data.complex.basic tactic.norm_num tactic.ring

lemma X (a b : ℤ) (n : ℕ) : (a + b)^(n + 2) =
  (a^2 + 2 * a * b + b^2) * (a + b)^n :=
by simp only [pow_add]; ring
#print X
example (n : nat) (m : int) : 2^(n+1) * m = 2 * 2^n * m :=
by simp only [pow_add]; ring

#eval ((∘) ∘ (∘)) (+) (*) 13 11 20
#eval (∘) ((∘) (+)) (*) 13 11 20
#eval (((∘) (+)) ∘ (*)) 13 11 20
#eval ((∘) (+)) (* 13) 11 20
#eval ((+) ∘ (* 13)) 11 20
#eval (+) (11 * 13) 20
#eval (11 * 13) + 20

example {X Y : Type*} : Π [nonempty X] [nonempty Y], nonempty (X × Y)
| ⟨x⟩ ⟨y⟩ := ⟨(x, y)⟩

#exit
import data.real.basic order.conditionally_complete_lattice
instance : lattice.conditionally_complete_linear_order_bot (with_bot ℝ) :=
by apply_instance

import data.zsqrtd.gaussian_int

#eval ((finset.range 200).filter
  (λ x, ∃ a b : fin (x + 1), a.1^2 + b.1^2 = x)).sort (≤)

₄
notation `ℤ[i]` := gaussian_int

open euclidean_domain
#eval nat.factors (8 * 74 + 2)
#eval gcd (⟨557, 55⟩ : ℤ[i]) 12049
#eval 32 ^ 2 + 105 ^ 2


#exit

import tactic.omega data.nat.modeq

inductive C : Type
| c1 : C
| c2 : C

inductive D : Type
| d1 : D
| d2 : D

def thing1 (c : C) (d : D) : D :=
c.rec
  (_) -- correct "don't know how to synthesize placeholder -- here's a helpful context"
  (_) -- correct

def thing2 (c : C) (d : D) : D :=
C.rec_on c
  (D.rec_on d _ _ )
  (_)

open nat
example (n : fin 70) : n % 7 = (n / 10 + 5 * (n % 10)) % 7 :=
begin
revert n,
exact dec_trivial,

end

example (n : ℤ) (d : ℕ) (h : (2 : ℚ) * (d * d : ℤ) = ((n * n : ℤ) : ℚ)) :
  2 * ((d : ℤ) * (d : ℤ)) = n * n :=
begin
  rw [← @int.cast_inj ℚ],
end

#exit
import analysis.normed_space.basic
open metric
variables
{V : Type*} [normed_group V] [complete_space V] [normed_space ℝ V]

def B' : set V := closed_ball 0 1

example : B' ⊆ ⋃ (a : V) (H : a ∈ (B' : set V)), ball a 0.5 :=
begin
  sorry
end

#exit

theorem add_comm (a b : ℕ) : begin
  apply eq,
  apply ((+) : ℕ → ℕ → ℕ),
  apply a,
  apply b,
  apply ((+) : ℕ → ℕ → ℕ),
  apply b,
  apply a,
end

#exit
import data.fintype

#eval (@finset.univ (fin 100 × fin 100 × fin 100) _).filter
  (λ k : fin 100 × fin 100 × fin 100, (k.1.1 ^ k.2.1.1 + 1) ∣ (k.1.1 + 1 : ℕ)^k.2.2.1
     ∧ k.1.1 > 1 ∧ k.2.1.1 > 1 ∧ k.2.2.1 > 1)

--import data.zmod.basic data.zmod.quadratic_reciprocity

example {k : ℕ+} (h : (3 ^ (2 ^ ((k - 1) : ℕ) : ℕ) :
  zmod (2 ^ (2 ^ (k : ℕ)) + 1)) = -1) : nat.prime (2 ^ (2 ^ (k : ℕ)) + 1) :=
let n : ℕ+ := ⟨3 ^ (2 ^ ((k - 1) : ℕ) : ℕ) + 1, nat.succ_pos _⟩ in
have p3 : nat.prime 3, by norm_num,
have cp3n : nat.coprime 3 n,
  begin
    dsimp [n, nat.coprime],
    erw [nat.gcd_rec, ← zmodp.val_cast_nat p3 (3 ^ 2 ^ (k - 1 : ℕ) + 1)],
    simp [zero_pow (nat.pow_pos (show 0 < 2, from dec_trivial) _)]
  end,
let u3 : units (zmod n) := (@zmod.units_equiv_coprime n).symm ⟨3, sorry⟩ in
have h3 : u3 ^ (n : ℕ) = 1, from _,
begin



end


import data.fintype

variable {α : Type*}

open finset

theorem fintype.card_subtype_lt [fintype α] (p : α → Prop) [decidable_pred p]
  {x : α} (hx : ¬ p x) : fintype.card {x // p x} < fintype.card α :=
by rw [fintype.subtype_card]; exact finset.card_lt_card
  ⟨subset_univ _, classical.not_forall.2 ⟨x, by simp [*, set.mem_def]⟩⟩

#exit
import data.zmod.basic data.polynomial

open polynomial





inductive T : ℕ → Type
| mk : Π (n m : ℕ) (t : T m) (f : Π {n : ℕ}, T n), T n

#print T.rec

set_option trace.simplify.rewrite true





#print X

import data.nat.prime

open nat

lemma min_fac_le_div {n : ℕ} (pos : 0 < n) (np : ¬ prime n) : min_fac n ≤ n / min_fac n :=
match min_fac_dvd n with
| ⟨0, h0⟩     := absurd pos $ by rw [h0, mul_zero]; exact dec_trivial
| ⟨1, h1⟩     := begin
  rw mul_one at h1,
  rw [prime_def_min_fac, not_and_distrib, ← h1, eq_self_iff_true, not_true, or_false, not_le] at np,
  rw [le_antisymm (le_of_lt_succ np) (succ_le_of_lt pos), min_fac_one, nat.div_one]
end
| ⟨(x+2), hx⟩ := begin
  conv_rhs { congr, rw hx },
  rw [nat.mul_div_cancel_left _ (min_fac_pos _)],
  exact min_fac_le_of_dvd dec_trivial ⟨min_fac n, by rwa mul_comm⟩
end



#exit

import tactic.finish

lemma X (p : Prop): ¬(p ↔ ¬ p) := by ifinish
#print X
open multiset function

lemma eq_zero_iff_forall_not_mem {α : Type*} {s : multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
⟨λ h, h.symm ▸ λ _, not_false, eq_zero_of_forall_not_mem⟩

lemma map_eq_map {α β γ : Type*} (f : α → γ) (g : β → γ) {s : multiset α}
  (hs : s.nodup) {t : multiset β} (ht : t.nodup) (i : Πa∈s, β)
  (hi : ∀a ha, i a ha ∈ t) (h : ∀a ha, f a = g (i a ha))
  (i_inj : ∀a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) (i_surj : ∀b∈t, ∃a ha, b = i a ha) :
  s.map f = t.map g :=
have t = s.attach.map (λ x, i x.1 x.2),
  from (nodup_ext ht (nodup_map
      (show injective (λ x : {x // x ∈ s}, i x.1 x.2), from λ x y hxy,
        subtype.eq (i_inj x.1 y.1 x.2 y.2 hxy))
      (nodup_attach.2 hs))).2
    (λ x, by simp only [mem_map, true_and, subtype.exists, eq_comm, mem_attach];
      exact ⟨i_surj _, λ ⟨y, hy⟩, hy.snd.symm ▸ hi _ _⟩),
calc s.map f = s.pmap  (λ x _, f x) (λ _, id) : by rw [pmap_eq_map]
... = s.attach.map (λ x, f x.1) : by rw [pmap_eq_map_attach]
... = t.map g : by rw [this, multiset.map_map]; exact map_congr (λ x _, h _ _)

#exit
import tactic.ring

example (p : ℕ) : p / 2 * (p / 2) + p / 2 * (p / 2) + p % 2 * (p % 2) +
  (2 * (p / 2 * (p / 2)) + 4 * (p / 2) * (p % 2)) =
    (p % 2 + 2 * (p / 2)) * (p % 2 + 2 * (p / 2)) :=
begin
 ring,

end

example (n : ℕ) : n + n = 2 * n := by ring


import data.nat.prime

inductive option' (α : Sort*) : Sort*
| none {} : option'
| some : α → option'

def zmod (n : ℕ) (h : option' n.prime := option'.none) : Type := fin n

#exit
import data.zmod.basic algebra.euclidean_domain

def remainder_aux (a b : ℤ) : ℤ :=
if hb : b = 0 then a
else (a : zmod ⟨b.nat_abs, int.nat_abs_pos_of_ne_zero hb⟩).val_min_abs

def X : euclidean_domain ℤ :=
{ remainder := remainder_aux,
  quotient := λ a b, (a - remainder_aux a b) / b,
  quotient_zero := by simp [remainder_aux],
  quotient_mul_add_remainder_eq := λ a b,
    begin
      rw [remainder_aux, int.mul_div_cancel', sub_add_cancel],
      split_ifs with hb,
      { simp },
      { erw [← int.nat_abs_dvd,
          ← @zmod.eq_zero_iff_dvd_int ⟨b.nat_abs, int.nat_abs_pos_of_ne_zero hb⟩],
        simp }
    end,
  r := λ x y, x.nat_abs < y.nat_abs,
  r_well_founded := measure_wf _,
  remainder_lt := λ a b hb0,
    by rw [remainder_aux, dif_neg hb0];
      exact lt_of_le_of_lt (zmod.nat_abs_val_min_abs_le _) (nat.div_lt_self
        (int.nat_abs_pos_of_ne_zero hb0) dec_trivial),
  mul_left_not_lt := λ a b hb0, not_lt_of_le $
    by rw [int.nat_abs_mul];
      exact le_mul_of_one_le_right' (nat.zero_le _) (int.nat_abs_pos_of_ne_zero hb0) }

#exit
import algebra.field data.rat.basic data.nat.choose

#print axioms add_pow

#print inv_inv'
set_option trace.simplify.rewrite true
example (x : ℚ) : x⁻¹⁻¹ = x := by simp


@[simp] lemma sol_set_simplex (T : tableau m n) (hT : feasible T) (w : tableau m n → bool)
  (obj : fin m) : (T.simplex w obj hT).1.sol_set = T.sol_set :=
by simp [sol_set_eq_res_set_inter_dead_set]

import algebra.group_power

example (n : ℕ) (a b : ℤ) : (a * b) ^ n = a ^ n * b ^ n :=
begin
  induction n with n ih,

end

#exit
import data.equiv.basic data.int.basic data.set.intervals

def int.Ico_fin_equiv (a b : ℤ) : set.Ico a b ≃ fin (int.to_nat $ b - a) :=
calc set.Ico a b ≃ set.Ico 0 (b - a) :
  ⟨λ x, ⟨x.1 - a, sub_nonneg.2 x.2.1, add_lt_add_right x.2.2 _⟩,
  λ x, ⟨x.1 + a, le_add_of_nonneg_left x.2.1, lt_sub_iff_add_lt.1 x.2.2⟩,
  λ _, by simp, λ _, by simp⟩
 ... ≃ fin (int.to_nat $ b - a) :
  ⟨λ x, ⟨x.1.to_nat, int.coe_nat_lt.1 $
    by rw [int.to_nat_of_nonneg x.2.1, int.to_nat_of_nonneg (le_trans x.2.1 (le_of_lt x.2.2))];
      exact x.2.2⟩,
  λ x, ⟨x.1, int.coe_nat_nonneg _, begin
    have := int.coe_nat_lt.2 x.2,
    rwa [int.to_nat_of_nonneg] at this,
    cases b - a;
    simp only [int.to_nat, int.coe_nat_lt, nat.not_lt_zero, *] at *
  end⟩,
  λ x, by simp [int.to_nat_of_nonneg x.2.1],
  λ x, by simp⟩

def int.Ioo_fin_equiv (a b : ℤ) : set.Ioo a b ≃ fin (int.to_nat $ b - (a + 1)) :=
calc set.Ioo a b ≃ set.Ico (a + 1) b : equiv.set.of_eq (by simp [set.ext_iff, int.add_one_le_iff])
... ≃ _ : int.Ico_fin_equiv _ _

def int.Ioc_fin_equiv (a b : ℤ) : set.Ioc a b ≃ fin (int.to_nat $ b - a) :=
calc set.Ioc a b ≃ set.Ioo a (b + 1) : equiv.set.of_eq (by simp [set.ext_iff, int.lt_add_one_iff])
... ≃ fin (int.to_nat $ (b + 1) - (a + 1)) : int.Ioo_fin_equiv _ _
... ≃ fin (int.to_nat $ b - a) : ⟨fin.cast (by simp), fin.cast (by simp),
  λ _, fin.eq_of_veq rfl, λ _, fin.eq_of_veq rfl⟩

def int.Icc_fin_equiv (a b : ℤ) : set.Icc a b ≃ fin (int.to_nat $ b + 1 - a) :=
calc set.Icc a b ≃ set.Ico a (b + 1) : equiv.set.of_eq (by simp [set.ext_iff, int.lt_add_one_iff])
... ≃ fin (int.to_nat $ b + 1 - a) : int.Ico_fin_equiv _ _

class good (n : ℕ).

instance good4 : good 4 := good.mk _

local attribute [-pattern] nat.add has_add.add
local attribute [irreducible] has_add.add
local attribute [reducible] nat.mul

example : good (2 + 2) := infer_instance
example : good (2 * 2) := infer_instance
example : good (0 + 4) := infer_instance
#print has_add.add
#print nat.add
#print has_mul.mul
#print nat.mul
#exit
import tactic

inductive next_to : ℤ → ℤ → Prop
| left : ∀ x, next_to x (x + 1)
| right : ∀ x, next_to (x + 1) x

def next_to (a b : ℤ) := ∃ d ∈ ([-1, 1] : list ℤ), a + d = b

lemma next_to.symm {a b : ℤ} (hab : next_to a b) : next_to b a :=
by rcases hab with ⟨x, hx₁, hx₂⟩;
  exact ⟨-x, by simpa [eq_neg_iff_eq_neg, eq_comm, or_comm] using hx₁, by rw ← hx₂; simp⟩

#exit
#print tc
inductive tc' {α : Type*} (r : α → α → Prop) : α → α → Prop
| base : ∀ {x y}, r x y → tc' x y
| base_trans : ∀ {x y z}, r x y → tc' y z → tc' x z

lemma tc'.trans {α : Type*} (r : α → α → Prop) {x y z}
  (hxy : tc' r x y) : tc' r y z → tc' r x z :=
tc'.rec_on hxy (λ _ _, tc'.base_trans)
  (λ x y b hxy hyb ih hbz, tc'.base_trans hxy (ih hbz))


#print tc
#exit
example : (1 : ℕ) = 1 + @has_zero.zero ℕ ⟨1⟩ :=
begin
  rw add_zero,

end

#exit
import data.list.basic

inductive unit2 : Type
| star : unit2

instance : has_repr unit2 := ⟨λ x, "9"⟩

@[instance, priority 10000] def x : has_repr unit := ⟨λ x, punit.rec_on x "1"⟩
set_option profiler true
#eval if (list.range 1000000).sum = 999999 * 500000 then unit2.star else unit2.star

#eval if (list.range 1000000).sum = 999999 * 500000 then () else ()

#exit
import data.list

open list

lemma filter_false' {α : Type*} (l : list α) : l.filter (λ _, false) = [] := filter_false _

example (xs : list ℕ) : xs.filter (λ x, ¬true) = [] :=
by simp only [not_true]; convert filter_false' xs

example (xs : list ℕ) : xs.filter (λ x, ¬true) = [] :=
by simp only [not_true]; rw ← filter_false' xs; congr

#exit
import algebra.big_operators tactic.ring

def ssquares : ℕ → ℕ
| 0     := 0
| (n+1) := (n+1)*(n+1) + (ssquares n)

theorem ssquares_formula (n : ℕ) : 6*(ssquares n) = n*(n+1)*(2*n+1) :=
nat.rec_on n rfl -- trivial base case
(
assume k,
assume h :  6*(ssquares k) = k*(k+1)*(2*k+1),
show 6*(ssquares (k+1)) = (k+1)*((k+1)+1)*(2*(k+1)+1), from
calc
6*(ssquares (k+1)) = 6*((k+1)*(k+1) + (ssquares k)) : rfl
    ... = 6*((k+1)*(k+1)) + k*(k+1)*(2*k+1) : by rw [left_distrib, h]
    ... = _ : by ring)

#exit
import group_theory.abelianization
#print axioms

#print quotient_group._to_additive
open tactic expr

meta def get_macro : expr → list name
| (mvar _ _ e) := get_macro e
| (local_const _ _ _ e) := get_macro e
| (app e₁ e₂)        := get_macro e₁ ++ get_macro e₂
| (lam _ _ e₁ e₂)    := get_macro e₁ ++ get_macro e₂
| (pi _ _ e₁ e₂)     := get_macro e₁ ++ get_macro e₂
| (elet _ e₁ e₂ e₃)   := get_macro e₁ ++ get_macro e₂ ++ get_macro e₃
| (macro m l)      := macro_def_name m :: l.bind get_macro
| _ := []

-- #eval get_macro `()

-- #print declaration.type
-- run_cmd do e ← get_env, let l : list name := environment.fold e []
--   (λ d l, let t := d.type in cond (expr.occurs `(macro_def) t) (d.to_name :: l)  l),
--   trace l, return ()

def repr_aux : name → string
| name.anonymous := "anonymous"
| (name.mk_string s n) := "mk_string " ++ s ++ " (" ++ repr_aux n ++ ")"
| (name.mk_numeral i n) := "mk_numeral " ++ repr i ++ repr_aux n

run_cmd tactic.add_decl (declaration.defn `sorry [] `(nat) `(0)
  (reducibility_hints.opaque) tt)

def X : false := sorry

lemma Y : false := X
#print axioms
#eval (is_sorry `(X)).is_some

run_cmd do d ← get_decl `sorry, trace d.value, return ()

run_cmd do d ← get_decl `X, trace ((get_macro d.value).map repr_aux)
#print macro_def
def X := by tactic.exact $ macro prod.fst [var 0]
#print tactic.exact

#print expr

#exit
import tactic.norm_num

example : ∃ a b c : ℤ, a^3 + b^3 + c^3 = 42 :=
⟨-80538738812075974, 80435758145817515, 12602123297335631, by norm_num⟩

#exit
inductive T : Type
| foo : T → T

def X : T → T := T.foo

set_option trace.compiler.optimize_bytecode true

#eval X

#exit
import data.zsqrtd.gaussian_int data.list.basic

set_option profiler true
#eval (((((list.range 100).product (list.range 10)).product
  ((list.range 10).product (list.range 10))).map
    (λ a : (nat × nat) × (nat × nat),
      (zsqrtd.mk (int.of_nat a.1.1) (int.of_nat a.1.2) : gaussian_int) /
        ⟨int.of_nat a.2.1, int.of_nat a.2.2⟩)).sum
--5.18 seconds to 1.62 ms



#eval euclidean_domain.gcd
  (⟨35,2⟩ : gaussian_int) 15
#exit
import algebra.big_operators

@[inline] def ack : nat → nat → nat
| 0     y     := y+1
| (x+1) 0     := ack x 1
| (x+1) (y+1) := ack x (ack (x+1) y)

def P : ℕ → Prop := λ n, n < 2

instance : decidable_pred P := λ _, nat.decidable_lt _ _

def X (n : ℕ) : ℕ := if P n then 0 else ack 100 100

set_option trace.compiler.code_gen true
#eval if P 0 then 0 else ack 100 100


#exit

import category_theory.category

open category_theory

variables {obj : Type*} [category obj] (X : obj)
#print nat.add
#exit
import data.zmod.basic

theorem test_ind (n : nat) : (3^n -1) % 2 = 0 :=
have (3 : zmod 2) ^ n - 1 = 0, by simp [show (3 : zmod 2) = 1, from rfl],
have h12 : 1 ≤ 3 ^ n, from by rw ← nat.pow_eq_pow; exact one_le_pow_of_one_le dec_trivial _,
(@zmod.eq_iff_modeq_nat 2 (3 ^ n - 1) 0).1 $ by rw [nat.cast_sub]; simpa



theorem test_ind' (n : nat) : (3^n -1) % 2 = 0 :=
nat.rec_on n rfl
  (λ n ih,
    let ⟨a, ha⟩ := (nat.dvd_iff_mod_eq_zero _ _).2 ih in
    _)





#exit
import data.equiv.basic

#print environment.mk_std
#print acc
universe u
variables {α : Type u} (r : α → α → Prop)

inductive acc2 : α → Type u
| intro (x : α) (h : ∀ y, r y x → acc2 y) : acc2 x

def acc_of_acc2 (a : α) : acc2 r a → acc r a :=
λ h, begin
  induction h,
  refine acc.intro _ (λ _ _, _),
  apply h_ih,
  assumption
end

def acc2_of_acc (a : α) : acc r a → acc2 r a :=
λ h, begin
  induction h,
  refine acc2.intro _ (λ _ _, _),
  apply h_ih,
  assumption
end
set_option pp.proofs true
def acc2_equiv_acc (a : α) : acc2 r a ≃ acc r a :=
{ to_fun := acc_of_acc2 _ _,
  inv_fun := acc2_of_acc _ _,
  left_inv := λ h, begin
    induction acc_of_acc2 _ _ h,
    dsimp [acc2_of_acc] at *,
    induction h_1,
    simp,
    simp [ih] at *, end,
  right_inv := λ _, rfl

  end }

#print acc2.rec

#exit
open tactic
run_cmd
  do let e := environment.mk_std 0,
    tactic.trace (repr (environment.is_inductive e `nat))

run_cmd
  do let e := environment.mk_std 0,
    let t := e.fold 0 (λ _, nat.succ) in
    trace (repr t)

run_cmd
  do e ← tactic.get_env,
    tactic.trace (repr (environment.is_inductive e `nat))

#print environment

#print nat

import init.data.nat

#eval 1 + 1

#exit
import data.nat

import algebra.ordered_group

#print nat


open tactic expr declaration lean reducibility_hints
#print unify


def n_id : ℕ → ℕ
| 0 := 0
| (k+1) := k+1

set_option pp.all true

#print n_id -- n_id._main
#print declaration

def reducibility_hints.to_string : Π (h : reducibility_hints), string
| opaque  := "opaque"
| abbrev  := "abbrev"
| (regular n b)  := "regular " ++ repr n ++ " " ++ repr b

meta def get_reducibility_hints : Π (d : declaration), string
| (defn _ _ _ _ h _) := h.to_string
| _ := "none"

def n_id2 := n_id._main

example : n_id = n_id2 := rfl -- succeeds

example : n_id = λ n, n_id n := rfl -- fails

run_cmd tactic.add_decl $ declaration.defn `n_id3 [] `(ℕ → ℕ) `(n_id._main) (regular 5 ff) tt

example : n_id = λ n, n_id3 n := rfl

#eval do t ← get_decl `n_id2, trace $ get_reducibility_hints t

example : n_id = λ n, n_id n := by {dsimp, refl} -- succeeds
-- proof term:
-- @id.{0} (@eq.{1} (nat → nat) n_id (λ (n : nat), n_id n)) (@eq.refl.{1} (nat → nat) n_id)

example : n_id = λ n, n_id n := -- fails
@id.{0} (@eq.{1} (nat → nat) n_id (λ (n : nat), n_id n)) (@eq.refl.{1} (nat → nat) n_id)

example : n_id2 = λ n, n_id2 n := rfl -- succeeds

example : n_id = λ n, n_id2 n := rfl -- succeeds

def nat2 := nat
instance : has_one nat2 := ⟨(0 : ℕ)⟩
example : (0 : ℕ) = (1 : nat2) := rfl

run_cmd do
  let trace_unify (e1 e2 : expr) : tactic unit := (do
    trace $ "try to unify " ++ to_string e1 ++ " with " ++ to_string e2,
    unify e1 e2 transparency.all tt,
    trace $ "unify successful between " ++ to_string e1 ++ " with " ++ to_string e2),
  let c1 : expr tt := const `nat.pred [],
  let c2 : expr tt := const `nat.pred._main [],
  trace_unify c1 c2, -- success
  trace "",
  let eta_nat t := lam `n binder_info.default (const `nat []) $ mk_app t [var 0],
 -- trace_unify (eta_nat c1) (eta_nat c2), -- failure!
  trace_unify `(@has_one.one nat2 _) `(@has_zero.zero ℕ _)

run_cmd tactic.add_decl $ declaration.thm `blah []
  `(@has_one.one nat2 _ = (0 : ℕ)) (pure `(eq.refl (0 : ℕ)))

#print unify
run_cmd tactic.add_decl $ declaration.thm `prod.fst_def []
    `(∀ α β : Type, ∀ x : α × β, x.fst = prod.rec (λ a b, a) x)
    (pure `(λ α β : Type, λ x : α × β, eq.refl x.fst))
#print blah

attribute [_refl_lemma] prod.fst_def

#print prod.fst_def

#print nat.pred
#print nat.pred._main
#print nat.pred.equations._eqn_1

def f : ℕ → ℕ := nat.pred._main

def g : ℕ → ℕ := f

local attribute [reducible] nat.pred

run_cmd tactic.add_decl $ declaration.thm `nat.pred_eq_pred_main []
  `((λ n, nat.pred n) = λ n, nat.pred._main n) (pure `(@rfl _ nat.pred))

example : (λ n, nat.pred n) = (λ n, nat.pred._main n) := eq.refl nat.pred

#exit
import algebra.ordered_ring

#print nonneg_of_mul_nonneg_left
#print nonneg_of_mul_nonneg_right
#print nonpos_of_mul_nonpos_left
#print nonpos_of_mul_nonpos_right
#print pos_of_mul_pos_left
#print pos_of_mul_pos_right
#print neg_of_mul_neg_left
#print neg_of_mul_neg_right
#print declaration

#eval do d ← tactic.get_decl `nat.rec, tactic.trace d.type.to_raw_fmt.to_string, return ()

variables {α : Type*} [linear_ordered_semiring α] {a b c : α}
#print mul_pos_of_neg_of_neg
lemma neg_of_mul_pos_left (h : 0 < a * b) (hb : b ≤ 0) : a < 0 :=
lt_of_not_ge (λ ha, absurd h (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha hb)))

lemma neg_of_mul_pos_right (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
lt_of_not_ge (λ hb, absurd h (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg ha hb)))

lemma pos_of_mul_neg_left (h : a * b < 0) (hb : 0 ≤ b) : 0 < a :=
lt_of_not_ge (λ ha, absurd h (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos _ _)))

lemma nonneg_of_mul_nonpos_left (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
le_of_not_gt (λ ha, absurd h (not_le_of_gt (mul_pos_of_neg_of_neg _  _)))

#exit
import data.nat.basic

local attribute [instance] classical.dec

lemma Q6 (a b : ℕ) (hab : (a * b + 1) ∣ a ^ 2 + b ^ 2) :
  ¬ ∀ k : ℕ, k^2 * (a * b + 1) ≠ a ^ 2 + b ^ 2:=
λ hk,
have h : ∃ a b, (∀ k : ℕ, k^2 * (a * b + 1) ≠ a ^ 2 + b ^ 2) ∧ (a * b + 1) ∣ a ^ 2 + b ^ 2,
  from ⟨a, b, hk, hab⟩,
let i := nat.find h in
let ⟨j, hj⟩ := nat.find_spec h in
let ⟨n, hn⟩ := hj.2 in
let i' := n * j - i in
have hi' : i' < i, from sorry,
nat.find_min h hi' ⟨(j^2 - n) / i, begin



end⟩

#exit
import data.rat.basic

@[simp] lemma int.square_zero {n : ℤ} : n^2 = 0 ↔ n = 0 :=
begin
  rw pow_two,
  split,
  { contrapose!, intro h,
    rcases lt_trichotomy n 0 with H|rfl|H,
    { apply ne_of_gt, exact mul_pos_of_neg_of_neg H H },
    { contradiction },
    { apply ne_of_gt, exact mul_pos H H } },
  { rintro rfl, simp },
end

lemma int.square_pos {n : ℤ} : n^2 > 0 ↔ n ≠ 0 :=
begin
  rw ←not_iff_not, push_neg,
  split,
  { rw ←int.square_zero, intro h, apply le_antisymm h, exact pow_two_nonneg n },
  { rintro rfl, simp [pow_two] }
end

variables {a b : ℤ} (h : a*b + 1 ∣ a^2 + b^2)
include h

lemma nz : a*b + 1 ≠ 0 :=
begin
  cases h with c h,
  contrapose! h,
  simp [h],
  rw [add_eq_zero_iff' (pow_two_nonneg _) (pow_two_nonneg _)],
  rw [int.square_zero, int.square_zero],
  rintro ⟨rfl, rfl⟩,
  simpa using h,
end

lemma q6_aux (a b : ℤ) (n : ℕ) (hn : a^2 + b^2 = n * (a * b + 1)),
  ∃ k : ℤ, a^2 + b^2 = k^2 * (a * b + 1) :=
begin


end

lemma q6 (a b : ℤ) (h : a*b + 1 ∣ a^2 + b^2) :
  ∃ q : ℚ, q^2 = (a^2 + b^2)/(a*b + 1) :=
begin
  cases q6_aux a b h with k hk,
  use k,
  rw_mod_cast hk, rw rat.mk_eq_div,
  simp,
  rw mul_div_cancel,
  norm_cast,
  simpa using nz h,
end

#exit
import data.fintype

instance psigma.fintype {α : Type*} {β : α → Type*} [fintype α] [∀ a, fintype (β a)] :
  fintype (Σ' a, β a) :=
fintype.of_equiv _ (equiv.psigma_equiv_sigma _).symm

instance psigma.fintype_prop_left {α : Prop} {β : α → Type*} [∀ a, fintype (β a)] [decidable α] :
  fintype (Σ' a, β a) :=
if h : α then fintype.of_equiv (β h) ⟨λ x, ⟨h, x⟩, psigma.snd, λ _, rfl, λ ⟨_, _⟩, rfl⟩
else ⟨∅, λ x, h x.1⟩

instance psigma.fintype_prop_right {α : Type*} {β : α → Prop} [∀ a, decidable (β a)] [fintype α] :
  fintype (Σ' a, β a) :=
fintype.of_equiv {a // β a} ⟨λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, rfl, λ ⟨x, y⟩, rfl⟩

instance psigma.fintype_prop_prop {α : Prop} {β : α → Prop} [∀ a, decidable (β a)] [decidable α] :
  fintype (Σ' a, β a) :=
if h : ∃ a, β a then ⟨{⟨h.fst, h.snd⟩}, λ ⟨_, _⟩, by simp⟩ else ⟨∅, λ ⟨x, y⟩, h ⟨x, y⟩⟩

#exit
import order.conditionally_complete_lattice
import data.real.basic

open classical set lattice

variables (Inf_one : real.Inf {(1:ℝ)} = 1)
          (Inf_zero_one : real.Inf {(0:ℝ), (1:ℝ)} = 0)
include Inf_one Inf_zero_one

lemma foo {K : set ℕ} (h : K = {0}) : (⨅ w : ℕ, (⨅ H : w ∈ K, (1:ℝ))) = 0 :=
have Inf_one : real.Inf {(1 : ℝ)} = 1, from
  le_antisymm (real.Inf_le _ ⟨1, by simp {contextual := tt}⟩ (by simp))
    ((real.le_Inf _ ⟨1, set.mem_singleton (1 : ℝ)⟩ ⟨1, by simp {contextual := tt}⟩).2
      (by simp {contextual := tt})),
show real.Inf (range (λ w, real.Inf (range (λ (H : w ∈ K), (1:ℝ))))) = (0:ℝ), from
have h_range : range (λ w, real.Inf (range (λ (H : w ∈ K), (1:ℝ)))) = {(0:ℝ), (1:ℝ)},
begin
  ext, rw mem_range, split,
  rintros ⟨n, rfl⟩,
  by_cases h₂ : n = (0:ℕ),
  have : n ∈ K, finish,
  have : range (λ (H : n ∈ K), (1:ℝ)) = {(1:ℝ)}, ext, finish,
  rw [this, Inf_one], finish,

  have : n ∉ K, finish,
  have : range (λ (H : n ∈ K), (1:ℝ)) = (∅:set ℝ), ext, finish,
  rw this, show lattice.Inf ∅ ∈ {(0:ℝ), (1:ℝ)}, rw real.Inf_empty, finish,

  simp only [mem_singleton_iff, mem_insert_iff, set.insert_of_has_insert],
  intro h, cases h with h h,
  use 0,
  have : range (λ (H : 0 ∈ K), (1:ℝ)) = {1}, ext, finish,
  rw [this, Inf_one], finish,

  use 1,
  have : range (λ (H : 1 ∈ K), (1:ℝ)) = ∅, ext, finish,
  rw this, show lattice.Inf ∅ = x, rw real.Inf_empty, finish
end,
begin
  rw h_range, exact Inf_zero_one
end

lemma foo' {K : set ℕ} (h : K = {0}) : (⨅ w ∈ K, (1:ℝ)) = 1 :=
show lattice.Inf (range (λ w, lattice.Inf (range (λ (H : w ∈ K), (1:ℝ))))) = (1:ℝ),
from
have ∀ w : ℕ, (range (λ (H : w ∈ K), (1:ℝ)))
have (range (λ w, lattice.Inf (range (λ (H : w ∈ K), (1:ℝ))))) = {(1 : ℝ)},
  from begin simp [h, set.ext_iff], end,
begin


end


#exit
import ring_theory.noetherian ring_theory.principal_ideal_domain


example {K : Type*} [discrete_field K] : is_noetherian_ring K := by apply_instance --works
example {K : Type*} [discrete_field K] : is_noetherian K K := by apply_instance
#exit
import algebra.ordered_Ring

lemma int.succ_ne_self (x : ℤ) : x + 1 ≠ x :=
(ne_of_lt (lt_add_one x)).symm

#exit
import algebra.ordered_ring algebra.group_power tactic.ring

variables {R : Type*} [discrete_linear_ordered_field R]

lemma discriminant_le_zero {a b c : R} (h : ∀ x : R,  0 ≤ a*x*x + b*x + c) :
  b*b - 4*a*c ≤ 0 :=
have complete_square : ∀ x, (a * x * x + b * x + c) * 4 * a =
  (2 * a * x + b) ^ 2 - (b * b - 4 * a * c) :=
λ x, by ring,
begin
  rw [sub_nonpos],
  have := h 0,
  simp at this,


end

#exit
set_option old_structure_cmd true

class has_coe_to_fun' (Γ dom cod : Type) :=
( to_fun : Γ → dom → cod )

instance has_coe_to_fun'.has_coe_to_fun (Γ α β : Type) [has_coe_to_fun' Γ α β] :
  has_coe_to_fun Γ := ⟨_, @has_coe_to_fun'.to_fun _ α β _⟩

structure add_group_hom (α β : Type) [add_group α] [add_group β] :=
( to_fun : α → β )
( map_add : ∀ (a b), to_fun (a + b) = to_fun a + to_fun b )

instance add_group_hom.coe_to_fun (α β : Type) [add_group α] [add_group β] :
  has_coe_to_fun' (add_group_hom α β) α β := ⟨add_group_hom.to_fun⟩

structure ring_hom (α β : Type) [ring α] [ring β] extends add_group_hom α β :=
( map_mul : ∀ (a b), to_fun (a * b) = to_fun a * to_fun b )
( map_one : to_fun 1 = 1 )

instance ring_hom.coe_to_fun (α β : Type*) [ring α] [ring β] :
  has_coe_to_fun' (ring_hom α β) α β := ⟨ring_hom.to_fun⟩

class has_map_add (Γ α β : Type) [has_coe_to_fun' Γ α β] [add_group α]
  [add_group β] :=
( map_add : ∀ (f : Γ) (a b : α), f (a + b) = f a + f b )

instance add_group_hom.has_map_add (α β : Type) [add_group α] [add_group β] :
  has_map_add (add_group_hom α β) α β :=
⟨add_group_hom.map_add⟩

instance ring_hom.has_map_add (α β : Type) [ring α] [ring β] : has_map_add (ring_hom α β) α β :=
⟨ring_hom.map_add⟩

attribute [simp] has_map_add.map_add

example (f : ring_hom ℤ ℤ) (a b : ℤ) : f a + f b = f (a + b) :=
begin
 rw has_map_add.map_add ℤ f,

end

#exit
import ring_theory.noetherian ring_theory.principal_ideal_domain

example {K : Type*} [discrete_field K] : is_noetherian_ring K := by apply_instance --works
example {K : Type*} [discrete_field K] : is_noetherian K K := by apply_instance --fails

def S {X Y : Type} (f : X → Y) : X → X → Prop := λ x₁ x₂, f x₁ = f x₂

example {X Y : Type} (f : X → Y) : reflexive (S f) := λ x, rfl -- works
example {X Y : Type} (f : X → Y) : reflexive (S f) := λ x, begin
refl, end -- fails!

#exit

example {R : Type*} [monoid R] {a b c : R} (hab : a * b = 1) (hca : c * a = 1) : b = c :=
by rw [← one_mul b, ← hca, mul_assoc, hab, mul_one]

#exit
import data.real.cardinality group_theory.quotient_group set_theory.ordinal
#print real.topological_space
open cardinal

instance rat_cast_is_add_group_hom : is_add_group_hom (coe : ℚ → ℝ) :=
{ to_is_add_hom := { map_add := by simp } }

instance : is_add_subgroup (set.range (coe : ℚ → ℝ)) :=
is_add_group_hom.range_add_subgroup _

lemma rat_lt_real : mk ℚ < mk ℝ :=
calc mk ℚ = mk ℕ : quotient.sound ⟨denumerable.equiv₂ _ _⟩
... = omega : mk_nat
... < 2 ^ omega.{0} : cantor _
... = mk ℝ : mk_real.symm

lemma omega_eq_set_range_coe : omega.{0} = mk (set.range (coe : ℚ → ℝ)) :=
by rw [← mk_rat]; exact quotient.sound ⟨equiv.set.range _ rat.cast_injective⟩

lemma ne_zero_of_nonempty {α : Type*} [hn : nonempty α] : mk α ≠ 0 :=
λ f, nonempty.elim hn (λ a, pempty.elim (classical.choice (quotient.exact f) a))

noncomputable lemma real_equiv_real_mod_rat : ℝ ≃ quotient_add_group.quotient
  (set.range (coe : ℚ → ℝ)) :=
have ℝ ≃ quotient_add_group.quotient (set.range (coe : ℚ → ℝ)) ×
  (set.range (coe : ℚ → ℝ)) := is_add_subgroup.add_group_equiv_quotient_times_subgroup _,
calc ℝ ≃ quotient_add_group.quotient (set.range (coe : ℚ → ℝ)) ×
  (set.range (coe : ℚ → ℝ)) : is_add_subgroup.add_group_equiv_quotient_times_subgroup _
... ≃ quotient_add_group.quotient (set.range (coe : ℚ → ℝ)) : classical.choice $
  quotient.exact $ show mk _ * mk _ = mk _,
begin
  have hR : cardinal.mk _ = cardinal.mk _ * cardinal.mk _ := quotient.sound ⟨this⟩,
  have hQ :  cardinal.mk ℚ = cardinal.mk (set.range (coe : ℚ → ℝ)),
    from quotient.sound ⟨equiv.set.range _ (λ _, by simp)⟩,
  have : cardinal.mk (set.range (coe : ℚ → ℝ)) <
    cardinal.mk (quotient_add_group.quotient (set.range (coe : ℚ → ℝ))) :=
    begin
      refine lt_of_not_ge _,
      assume h,
      rw [mul_comm, mul_eq_max_of_omega_le_left (le_of_eq omega_eq_set_range_coe)
        (@ne_zero_of_nonempty _ ⟨(0 : quotient_add_group.quotient _)⟩),
        max_eq_left h, ← hQ] at hR,
      exact absurd rat_lt_real (by rw hR; exact lt_irrefl _), apply_instance
    end,
  rw [mul_comm, mul_eq_max_of_omega_le_left (le_of_eq omega_eq_set_range_coe),
    max_eq_right (le_of_lt this)],
  exact (@ne_zero_of_nonempty _ ⟨(0 : quotient_add_group.quotient _)⟩)
end

noncomputable def f : ℝ → ℝ := real_equiv_real_mod_rat.symm ∘ quotient_add_group.mk

lemma thingy_aux (s : set ℝ) (hs : is_open s) (hsn : s ≠ ∅)
  (x : quotient_add_group.quotient (set.range (coe : ℚ → ℝ))) :
  ∃ y ∈ s, quotient_add_group.mk y = x :=
let ⟨a, ha⟩ := set.exists_mem_of_ne_empty hsn in
let ⟨b, hb⟩ := @quotient.exists_rep _ (id _) x in
let ⟨q, hq⟩ := set.exists_mem_of_ne_empty (mem_closure_iff.1
  (dense_inducing.dense dense_embedding_of_rat.to_dense_inducing a) s hs ha) in
let ⟨r, hr⟩ := set.exists_mem_of_ne_empty (mem_closure_iff.1
  (dense_inducing.dense dense_embedding_of_rat.to_dense_inducing (-b))
  ((λ x, b + (x + q)) ⁻¹' s)
   (continuous_add continuous_const
     (continuous_add continuous_id continuous_const) s hs)
   (by rw [set.mem_preimage, add_neg_cancel_left]; exact hq.1)) in
⟨_, hr.1, begin
  rw [← hb],
  refine quotient.sound' _,
  show _ ∈ set.range (coe : ℚ → ℝ),
  simp [-set.mem_range],
  exact is_add_submonoid.add_mem (is_add_subgroup.neg_mem hq.2)
    (is_add_subgroup.neg_mem hr.2)
end⟩

lemma thingy (s : set ℝ) (hs : is_open s) (hsn : s ≠ ∅) (x : ℝ) : ∃ y ∈ s, f y = x :=
let ⟨y, hy⟩ := thingy_aux s hs hsn (real_equiv_real_mod_rat x) in
⟨y, hy.fst, by rw [f, function.comp_app, hy.snd, equiv.symm_apply_apply]⟩

#exit
import data.fintype.basic data.zmod.basic

open finset equiv

example : ∀ {n : ℕ} (g : fin (n + 1) → fin n),
  ∃ (f₁ f₂ : perm (fin (n + 1))), ∀ x, (f₁ x : ℕ) + f₂ x ≡ x [MOD (n+1)]
| 0     g := ⟨1, 1, by simp [nat.modeq]⟩
| (n+1) g := begin



end

#exit
import data.quot logic.basic

meta def choice {α : Sort*} {β : α → Sort*} : (Π a, trunc (β a)) → trunc (Π a, β a) :=
λ f, trunc.mk (λ a, quot.unquot (f a))

def decidable_true (choice : Π {α : Sort*} {β : α → Sort*}
  (f : Π a, trunc (β a)), trunc (Π a, β a)) : decidable true :=
trunc.rec_on_subsingleton (choice (id : trunc bool → trunc bool))
  (λ f, decidable_of_iff (f (trunc.mk tt) = f (trunc.mk ff))
    (by rw [subsingleton.elim (trunc.mk tt) (trunc.mk ff)]; exact eq_self_iff_true _))

#eval decidable_true @choice --ff


def bool_dec_eq_of_choice (choice : Π {α : Sort*} {β : α → Sort*} (f : Π a, trunc (β a)),
  trunc (Π a, β a)) : decidable_eq bool :=
trunc.rec_on_subsingleton (choice (id : trunc bool → trunc bool))
  (λ f a b, decidable_of_iff (f (trunc.mk a) = f (trunc.mk b))
    ⟨_, _⟩)

def choice_computes {α : Sort*} {β : α → Sort*} (f : Π a, trunc (β a)) :
  ∀ a : α, trunc.lift_on (f a) (λ b, trunc.lift_on (choice f) (λ f, f a = b)
    sorry) sorry

example : false :=
begin
  have := choice_computes (id : trunc bool → trunc bool) (trunc.mk tt),

  dsimp [trunc.lift_on, trunc.lift, trunc.mk] at this,


end

section
parameter (p : Prop)

def r : setoid bool :=
  { r := λ x y : bool, p ∨ x = y,
    iseqv := ⟨λ _, or.inr rfl,
      λ x y hxy, hxy.elim or.inl (or.inr ∘ eq.symm),
      λ x y z hxy hyz, hxy.elim or.inl
        (λ hxy, hyz.elim or.inl (λ hyz, or.inr $ by rw [hxy, hyz]))⟩ }

def suspension : Type := quotient r

noncomputable lemma g : trunc (Π s : suspension, {b : bool // @quotient.mk _ r b = s}) :=
choice (λ s, @quotient.rec_on_subsingleton _ (id _)
  (λ t, t = s → trunc {b : bool // @quotient.mk _ r b = s}) _ s
    (λ b hb, trunc.mk ⟨b, hb⟩) rfl)

noncomputable lemma prop_decidable : decidable p :=
trunc.rec_on_subsingleton g
  (λ g', let g := λ s, (g' s).val in
    have quot_mk_g : ∀ s, quotient.mk' (g s) = s, from λ s, (g' s).2,
    have g_injective : function.injective g, from
      function.injective_of_has_left_inverse ⟨_, quot_mk_g⟩,
    have p_iff_g_tt_eq_g_ff : p ↔ g (quotient.mk' tt) = g (quotient.mk' ff),
      from ⟨λ hp, congr_arg _ (quotient.sound' (or.inl hp)),
        λ h, (@quotient.exact _ (id _) _ _ (g_injective h)).elim
          id
          (λ h, bool.no_confusion h)⟩,
    decidable_of_iff _ p_iff_g_tt_eq_g_ff.symm)


#exit
import data.finsupp order.complete_lattice algebra.ordered_group data.mv_polynomial
import algebra.order_functions

namespace multiset
variables {α : Type*} [decidable_eq α]

def to_finsupp (s : multiset α) : α →₀ ℕ :=
{ support := s.to_finset,
  to_fun := λ a, s.count a,
  mem_support_to_fun := λ a,
  begin
    rw mem_to_finset,
    convert not_iff_not_of_iff (count_eq_zero.symm),
    rw not_not
  end }

@[simp] lemma to_finsupp_support (s : multiset α) :
  s.to_finsupp.support = s.to_finset := rfl

@[simp] lemma to_finsupp_apply (s : multiset α) (a : α) :
  s.to_finsupp a = s.count a := rfl

@[simp] lemma to_finsupp_zero :
  to_finsupp (0 : multiset α) = 0 :=
finsupp.ext $ λ a, count_zero a

@[simp] lemma to_finsupp_add (s t : multiset α) :
  to_finsupp (s + t) = to_finsupp s + to_finsupp t :=
finsupp.ext $ λ a, count_add a s t

namespace to_finsupp

instance : is_add_monoid_hom (to_finsupp : multiset α → α →₀ ℕ) :=
{ map_zero := to_finsupp_zero,
  map_add  := to_finsupp_add }

end to_finsupp

@[simp] lemma to_finsupp_to_multiset (s : multiset α) :
  s.to_finsupp.to_multiset = s :=
ext.2 $ λ a, by rw [finsupp.count_to_multiset, to_finsupp_apply]

end multiset

namespace finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ]

instance [preorder α] [has_zero α] : preorder (σ →₀ α) :=
{ le := λ f g, ∀ s, f s ≤ g s,
  le_refl := λ f s, le_refl _,
  le_trans := λ f g h Hfg Hgh s, le_trans (Hfg s) (Hgh s) }

instance [partial_order α] [has_zero α] : partial_order (σ →₀ α) :=
{ le_antisymm := λ f g hfg hgf, finsupp.ext $ λ s, le_antisymm (hfg s) (hgf s),
  .. finsupp.preorder }

instance [ordered_cancel_comm_monoid α] [decidable_eq α] :
  add_left_cancel_semigroup (σ →₀ α) :=
{ add_left_cancel := λ a b c h, finsupp.ext $ λ s,
  by { rw finsupp.ext_iff at h, exact add_left_cancel (h s) },
  .. finsupp.add_monoid }

instance [ordered_cancel_comm_monoid α] [decidable_eq α] :
  add_right_cancel_semigroup (σ →₀ α) :=
{ add_right_cancel := λ a b c h, finsupp.ext $ λ s,
  by { rw finsupp.ext_iff at h, exact add_right_cancel (h s) },
  .. finsupp.add_monoid }

instance [ordered_cancel_comm_monoid α] [decidable_eq α] :
  ordered_cancel_comm_monoid (σ →₀ α) :=
{ add_le_add_left := λ a b h c s, add_le_add_left (h s) (c s),
  le_of_add_le_add_left := λ a b c h s, le_of_add_le_add_left (h s),
  .. finsupp.add_comm_monoid, .. finsupp.partial_order,
  .. finsupp.add_left_cancel_semigroup, .. finsupp.add_right_cancel_semigroup }

attribute [simp] to_multiset_zero to_multiset_add

@[simp] lemma to_multiset_to_finsupp (f : σ →₀ ℕ) :
  f.to_multiset.to_finsupp = f :=
ext $ λ s, by rw [multiset.to_finsupp_apply, count_to_multiset]

def diagonal (f : σ →₀ ℕ) : finset ((σ →₀ ℕ) × (σ →₀ ℕ)) :=
((multiset.diagonal f.to_multiset).map (prod.map multiset.to_finsupp multiset.to_finsupp)).to_finset

lemma mem_diagonal {f : σ →₀ ℕ} {p : (σ →₀ ℕ) × (σ →₀ ℕ)} :
  p ∈ diagonal f ↔ p.1 + p.2 = f :=
begin
  erw [multiset.mem_to_finset, multiset.mem_map],
  split,
  { rintros ⟨⟨a, b⟩, h, rfl⟩,
    rw multiset.mem_diagonal at h,
    simpa using congr_arg multiset.to_finsupp h },
  { intro h,
    refine ⟨⟨p.1.to_multiset, p.2.to_multiset⟩, _, _⟩,
    { simpa using congr_arg to_multiset h },
    { rw [prod.map, to_multiset_to_finsupp, to_multiset_to_finsupp, prod.mk.eta] } }
end

lemma swap_mem_diagonal {n : σ →₀ ℕ} {f} (hf : f ∈ diagonal n) : f.swap ∈ diagonal n :=
by simpa [mem_diagonal, add_comm] using hf

@[simp] lemma diagonal_zero : diagonal (0 : σ →₀ ℕ) = {(0,0)} := rfl

lemma to_multiset_strict_mono : strict_mono (@to_multiset σ _) :=
λ m n h,
begin
  rw lt_iff_le_and_ne at h ⊢, cases h with h₁ h₂,
  split,
  { rw multiset.le_iff_count, intro s, rw [count_to_multiset, count_to_multiset], exact h₁ s },
  { intro H, apply h₂, replace H := congr_arg multiset.to_finsupp H, simpa using H }
end

lemma sum_lt_of_lt (m n : σ →₀ ℕ) (h : m < n) :
  m.sum (λ _, id) < n.sum (λ _, id) :=
begin
  rw [← card_to_multiset, ← card_to_multiset],
  apply multiset.card_lt_of_lt,
  exact to_multiset_strict_mono _ _ h
end

variable (σ)

def lt_wf : well_founded (@has_lt.lt (σ →₀ ℕ) _) :=
subrelation.wf (sum_lt_of_lt) $ inv_image.wf _ nat.lt_wf

-- instance : has_well_founded (σ →₀ ℕ) :=
-- { r := (<),
--   wf := lt_wf σ }

end finsupp

/-- Multivariate power series, where `σ` is the index set of the variables
and `α` is the coefficient ring.-/
def mv_power_series (σ : Type*) (α : Type*) := (σ →₀ ℕ) → α

namespace mv_power_series
open finsupp
variables {σ : Type*} {α : Type*} [decidable_eq σ]

def coeff (n : σ →₀ ℕ) (φ : mv_power_series σ α) := φ n

@[extensionality] lemma ext {φ ψ : mv_power_series σ α} (h : ∀ n, coeff n φ = coeff n ψ) : φ = ψ :=
funext h

lemma ext_iff {φ ψ : mv_power_series σ α} : φ = ψ ↔ (∀ n, coeff n φ = coeff n ψ) :=
⟨λ h n, congr_arg (coeff n) h, ext⟩

variables [comm_semiring α]

def monomial (n : σ →₀ ℕ) (a : α) : mv_power_series σ α := λ m, if m = n then a else 0

lemma coeff_monomial (m n : σ →₀ ℕ) (a : α) :
  coeff m (monomial n a) = if m = n then a else 0 := rfl

@[simp] lemma coeff_monomial' (n : σ →₀ ℕ) (a : α) :
  coeff n (monomial n a) = a := if_pos rfl

def C (a : α) : mv_power_series σ α := monomial 0 a

lemma coeff_C (n : σ →₀ ℕ) (a : α) :
  coeff n (C a : mv_power_series σ α) = if n = 0 then a else 0 := rfl

@[simp] lemma coeff_C_zero (a : α) : coeff 0 (C a : mv_power_series σ α) = a :=
coeff_monomial' 0 a

@[simp] lemma monomial_zero (a : α) : (monomial 0 a : mv_power_series σ α) = C a := rfl

def X (s : σ) : mv_power_series σ α := monomial (single s 1) 1

lemma coeff_X (n : σ →₀ ℕ) (s : σ) :
  coeff n (X s : mv_power_series σ α) = if n = (single s 1) then 1 else 0 := rfl

lemma coeff_X' (s t : σ) :
  coeff (single t 1) (X s : mv_power_series σ α) = if t = s then 1 else 0 :=
if h : t = s then by simp [h, coeff_X] else
begin
  rw [coeff_X, if_neg h],
  split_ifs with H,
  { have := @finsupp.single_apply σ ℕ _ _ _ t s 1,
    rw [if_neg h, H, finsupp.single_apply, if_pos rfl] at this,
    exfalso, exact one_ne_zero this, },
  { refl }
end

@[simp] lemma coeff_X'' (s : σ) :
  coeff (single s 1) (X s : mv_power_series σ α) = 1 :=
by rw [coeff_X', if_pos rfl]

section ring
variables (σ) (α) (n : σ →₀ ℕ) (φ ψ : mv_power_series σ α)

def zero : mv_power_series σ α := λ n, 0

instance : has_zero (mv_power_series σ α) := ⟨zero σ α⟩

@[simp] lemma coeff_zero : coeff n (0 : mv_power_series σ α) = 0 := rfl

@[simp] lemma C_zero : (C 0 : mv_power_series σ α) = 0 :=
ext $ λ n, if h : n = 0 then by simp [h] else by rw [coeff_C, if_neg h, coeff_zero]

def one : mv_power_series σ α := C 1

instance : has_one (mv_power_series σ α) := ⟨one σ α⟩

@[simp] lemma coeff_one :
  coeff n (1 : mv_power_series σ α) = if n = 0 then 1 else 0 := rfl

@[simp] lemma coeff_one_zero : coeff 0 (1 : mv_power_series σ α) = 1 :=
coeff_C_zero 1

@[simp] lemma C_one : (C 1 : mv_power_series σ α) = 1 := rfl

def add (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, coeff n φ + coeff n ψ

instance : has_add (mv_power_series σ α) := ⟨add σ α⟩

variables {σ α}

@[simp] lemma coeff_add : coeff n (φ + ψ) = coeff n φ + coeff n ψ := rfl

@[simp] lemma zero_add : (0 : mv_power_series σ α) + φ = φ := ext $ λ n, zero_add _

@[simp] lemma add_zero : φ + 0 = φ := ext $ λ n, add_zero _

lemma add_comm : φ + ψ = ψ + φ := ext $ λ n, add_comm _ _

lemma add_assoc (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ + φ₂) + φ₃ = φ₁ + (φ₂ + φ₃) :=
ext $ λ n, by simp

@[simp] lemma monomial_add (n : σ →₀ ℕ) (a b : α) :
  (monomial n (a + b) : mv_power_series σ α) = monomial n a + monomial n b :=
ext $ λ m, if h : m = n then by simp [h] else by simp [coeff_monomial, if_neg h]

@[simp] lemma C_add (a b : α) : (C (a + b) : mv_power_series σ α) = C a + C b :=
monomial_add 0 a b

variables (σ α)

def mul (φ ψ : mv_power_series σ α) : mv_power_series σ α :=
λ n, (finsupp.diagonal n).sum (λ p, coeff p.1 φ * coeff p.2 ψ)
instance : has_mul (mv_power_series σ α) := ⟨mul σ α⟩

variables {σ α}

lemma coeff_mul :
  coeff n (φ * ψ) = (finsupp.diagonal n).sum (λ p, coeff p.1 φ * coeff p.2 ψ) := rfl

@[simp] lemma C_mul (a b : α) : (C (a * b) : mv_power_series σ α) = C a * C b :=
ext $ λ n,
begin
  rw [coeff_C, coeff_mul],
  split_ifs,
  { subst n, erw [diagonal_zero, finset.sum_singleton, coeff_C_zero, coeff_C_zero] },
  { rw finset.sum_eq_zero,
    rintros ⟨i,j⟩ hij,
    rw mem_diagonal at hij, rw [coeff_C, coeff_C],
    split_ifs; try {simp * at *; done} }
end

@[simp] lemma zero_mul : (0 : mv_power_series σ α) * φ = 0 :=
ext $ λ n, by simp [coeff_mul]

@[simp] lemma mul_zero : φ * 0 = 0 :=
ext $ λ n, by simp [coeff_mul]

lemma mul_comm : φ * ψ = ψ * φ :=
ext $ λ n, finset.sum_bij (λ p hp, p.swap)
  (λ p hp, swap_mem_diagonal hp)
  (λ p hp, mul_comm _ _)
  (λ p q hp hq H, by simpa using congr_arg prod.swap H)
  (λ p hp, ⟨p.swap, swap_mem_diagonal hp, p.swap_swap.symm⟩)

@[simp] lemma one_mul : (1 : mv_power_series σ α) * φ = φ :=
ext $ λ n,
begin
  have H : ((0 : σ →₀ ℕ), n) ∈ (diagonal n) := by simp [mem_diagonal],
  rw [coeff_mul, ← finset.insert_erase H, finset.sum_insert (finset.not_mem_erase _ _),
    coeff_one_zero, one_mul, finset.sum_eq_zero, _root_.add_zero],
  rintros ⟨i,j⟩ hij,
  rw [finset.mem_erase, mem_diagonal] at hij,
  rw [coeff_one, if_neg, _root_.zero_mul],
  intro H, apply hij.1, simp * at *
end

@[simp] lemma mul_one : φ * 1 = φ :=
by rw [mul_comm, one_mul]

lemma mul_add (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  φ₁ * (φ₂ + φ₃) = φ₁ * φ₂ + φ₁ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, mul_add, finset.sum_add_distrib]

lemma add_mul (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ + φ₂) * φ₃ = φ₁ * φ₃ + φ₂ * φ₃ :=
ext $ λ n, by simp only [coeff_mul, coeff_add, add_mul, finset.sum_add_distrib]

lemma mul_assoc (φ₁ φ₂ φ₃ : mv_power_series σ α) :
  (φ₁ * φ₂) * φ₃ = φ₁ * (φ₂ * φ₃) :=
ext $ λ n,
begin
  simp only [coeff_mul],
  have := @finset.sum_sigma ((σ →₀ ℕ) × (σ →₀ ℕ)) α _ _ (diagonal n)
    (λ p, diagonal (p.1)) (λ x, coeff x.2.1 φ₁ * coeff x.2.2 φ₂ * coeff x.1.2 φ₃),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl,
    intros p hp, exact finset.sum_mul },
  have := @finset.sum_sigma ((σ →₀ ℕ) × (σ →₀ ℕ)) α _ _ (diagonal n)
    (λ p, diagonal (p.2)) (λ x, coeff x.1.1 φ₁ * (coeff x.2.1 φ₂ * coeff x.2.2 φ₃)),
  convert this.symm using 1; clear this,
  { apply finset.sum_congr rfl, intros p hp, rw finset.mul_sum },
  apply finset.sum_bij,
  swap 5,
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, exact ⟨(k, l+j), (l, j)⟩ },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, simp only [finset.mem_sigma, mem_diagonal] at H ⊢, finish },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, rw mul_assoc },
  { rintros ⟨⟨a,b⟩, ⟨c,d⟩⟩ ⟨⟨i,j⟩, ⟨k,l⟩⟩ H₁ H₂,
    simp only [finset.mem_sigma, mem_diagonal,
      and_imp, prod.mk.inj_iff, add_comm, heq_iff_eq] at H₁ H₂ ⊢,
    finish },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H, refine ⟨⟨(i+k, l), (i, k)⟩, _, _⟩;
    { simp only [finset.mem_sigma, mem_diagonal] at H ⊢, finish } }
end

instance : comm_semiring (mv_power_series σ α) :=
{ mul_one := mul_one,
  one_mul := one_mul,
  add_assoc := add_assoc,
  zero_add := zero_add,
  add_zero := add_zero,
  add_comm := add_comm,
  mul_assoc := mul_assoc,
  mul_zero := mul_zero,
  zero_mul := zero_mul,
  mul_comm := mul_comm,
  left_distrib := mul_add,
  right_distrib := add_mul,
  .. mv_power_series.has_zero σ α,
  .. mv_power_series.has_one σ α,
  .. mv_power_series.has_add σ α,
  .. mv_power_series.has_mul σ α }

instance C.is_semiring_hom : is_semiring_hom (C : α → mv_power_series σ α) :=
{ map_zero := C_zero _ _,
  map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_monoid_hom : is_add_monoid_hom (coeff n : mv_power_series σ α → α) :=
{ map_zero := coeff_zero _ _ _,
  map_add := coeff_add n }

instance : semimodule α (mv_power_series σ α) :=
{ smul := λ a φ, C a * φ,
  one_smul := λ φ, one_mul _,
  mul_smul := λ a b φ, by simp only [C_mul, mul_assoc],
  smul_add := λ a φ ψ, mul_add _ _ _,
  smul_zero := λ a, mul_zero _,
  add_smul := λ a b φ, by simp only [C_add, add_mul],
  zero_smul := λ φ, by simp only [zero_mul, C_zero] }

end ring

-- TODO(jmc): once adic topology lands, show that this is complete

end mv_power_series

namespace mv_power_series
variables {σ : Type*} {α : Type*} [decidable_eq σ] [comm_ring α]

protected def neg (φ : mv_power_series σ α) : mv_power_series σ α := λ n, - coeff n φ

instance : has_neg (mv_power_series σ α) := ⟨mv_power_series.neg⟩

@[simp] lemma coeff_neg (φ : mv_power_series σ α) (n) : coeff n (- φ) = - coeff n φ := rfl

lemma add_left_neg (φ : mv_power_series σ α) : (-φ) + φ = 0 :=
ext $ λ n, by rw [coeff_add, coeff_zero, coeff_neg, add_left_neg]

instance : comm_ring (mv_power_series σ α) :=
{ add_left_neg := add_left_neg,
  .. mv_power_series.has_neg, .. mv_power_series.comm_semiring }

instance C.is_ring_hom : is_ring_hom (C : α → mv_power_series σ α) :=
{ map_one := C_one _ _,
  map_add := C_add,
  map_mul := C_mul }

instance coeff.is_add_group_hom (n : σ →₀ ℕ) :
  is_add_group_hom (coeff n : mv_power_series σ α → α) :=
{ map_add := coeff_add n }

instance : module α (mv_power_series σ α) :=
{ ..mv_power_series.semimodule }

local attribute [instance, priority 0] classical.dec

noncomputable def inv_of_unit (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) : mv_power_series σ α
| n := if n = 0 then ↑u⁻¹ else
- ↑u⁻¹ * finset.sum (n.diagonal) (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
   if h : x.1 < n then inv_of_unit x.1 * coeff x.2 φ else 0)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, finsupp.lt_wf σ⟩],
  dec_tac := tactic.assumption }

end mv_power_series

#exit
import algebra.associated data.finsupp

variables {α : Type*} {σ : Type*} [ring α]

@[reducible] def mv_power_series (σ : Type*) (α : Type*) := (σ →₀ ℕ) → α

instance : has_zero $ mv_power_series σ α := ⟨λ _, 0⟩

def coeff  (x : (σ →₀ ℕ))  (a : (σ →₀ ℕ) → α):= a x

local attribute [instance] classical.dec

def inv_of_unit (φ : mv_power_series σ α) (u : units α) (h : coeff 0 φ = u) : mv_power_series σ α
| n := if n = 0 then ↑u⁻¹ else
  - ↑u⁻¹ * finset.sum (n.diagonal) (λ (x : (σ →₀ ℕ) × (σ →₀ ℕ)),
    if h : x.1 < n then inv_of_unit x.1 * coeff x.2 φ else 0)
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, finsupp.lt_wf σ⟩] }

#exit
import data.finsupp
variables {σ : Type}

instance : preorder (σ →₀ ℕ) :=
{ le := λ f g, ∀ s, f s ≤ g s,
  le_refl := λ f s, le_refl _,
  le_trans := λ f g h Hfg Hgh s, le_trans (Hfg s) (Hgh s) }
#print finset.sum_le
lemma sum_lt_sum_of_lt (f g : σ →₀ ℕ) : f < g → f.sum (λ _, id) < g.sum (λ _, id) :=
begin
  assume hfg,
  cases  classical.not_forall.1 hfg.2 with i hi,
  rw finsupp.sum,

end

#exit
import set_theory.schroeder_bernstein

universe u

structure B := (C : Type u)

lemma eq.mpr_injective {α β : Sort u} (h : α = β) :
  function.injective (eq.mpr h) := λ _ _, by cases h; exact id

instance : inhabited B := ⟨⟨pempty⟩⟩

open function

example {α : Type u} (f : B.{u} ↪ α) : false :=
let g := B.C ∘ inv_fun f in
have hg : surjective g, from
  surjective_comp (λ x, ⟨B.mk x, rfl⟩) (inv_fun_surjective f.2),
let X : Type u := sigma g in
let a : α := classical.some (hg (X → Prop)) in
have ha : g a = (X → Prop), from classical.some_spec (hg (set X)),
cantor_injective (show set X → X, from λ s, ⟨a, by rw ha; exact s⟩)
  (λ x y h, by simp at *; exact eq.mpr_injective _ h)

#exit
import ring_theory.ideal_operations
universe u
variables {R : Type u} [comm_ring R]

def ar : lattice.complete_lattice (ideal R) := by apply_instance
#print lattice.lt
instance : ordered_comm_monoid (ideal R) :=
{ le := (≤),
  add_le_add_left := λ a b hab c, lattice.sup_le_sup (le_refl _) hab,
  lt_of_add_lt_add_left := λ a b c h, begin
    refine not_lt

  end,
  --add_left_cancel := _,
  ..ideal.comm_semiring,
  ..submodule.lattice.complete_lattice
  --show lattice.complete_lattice (ideal R), by apply_instance
  }

#exit
import data.multiset data.finsupp
import category_theory.natural_isomorphism category_theory.types category_theory.opposites category_theory.concrete_category

universe u

open category_theory

namespace category_theory.instances

@[reducible] def DecEq := bundled decidable_eq

instance (x : DecEq) : decidable_eq x := x.str

instance DecEq_category : category DecEq :=
{ hom := λ x y, x → y,
  id := λ x, id,
  comp := λ x y z f g, g ∘ f }

end category_theory.instances

open category_theory.instances

@[reducible] def Multiset : DecEq.{u} ⥤ Type u :=
{ obj := λ α, multiset α,
  map := λ α β, multiset.map,
  map_id' := λ α, funext multiset.map_id,
  map_comp' := λ α β γ f g, funext $ λ s, (multiset.map_map g f s).symm }

@[reducible] def Finsupp_nat : DecEq.{u} ⥤ Type u :=
{ obj := λ α, α →₀ ℕ,
  map := λ α β, finsupp.map_domain,
  map_id' := λ α, funext $ λ s, finsupp.map_domain_id,
  map_comp' := λ α β γ f g, funext $ λ s, finsupp.map_domain_comp }

theorem multiset.map_repeat {α : Type u} {β : Type*} (f : α → β) (x : α) (n : ℕ) :
  multiset.map f (multiset.repeat x n) = multiset.repeat (f x) n :=
nat.rec_on n rfl $ λ n ih, by rw [multiset.repeat_succ, multiset.map_cons, ih, multiset.repeat_succ]

theorem multiset.repeat_add {α : Type u} (x : α) (m n : ℕ) :
  multiset.repeat x (m + n) = multiset.repeat x m + multiset.repeat x n :=
nat.rec_on n (by rw [multiset.repeat_zero, add_zero, add_zero]) $ λ n ih,
by rw [multiset.repeat_succ, nat.add_succ, multiset.repeat_succ, multiset.add_cons, ih]

-- ⟨s.to_finset, λ x, s.count x, λ x, multiset.mem_to_finset.trans $ multiset.count_pos.symm.trans $ nat.pos_iff_ne_zero⟩
-- faster but less idiomatic
def Multiset_Finsupp_nat : Multiset.{u} ≅ Finsupp_nat.{u} :=
{ hom :=
  { app := λ α s, { to_fun := λ a, s.count a,
      support := s.to_finset,
      mem_support_to_fun := by simp [multiset.count_eq_zero] },
    naturality' := λ X Y f, begin
      dsimp, simp [function.funext_iff, finsupp.ext_iff],
      unfold_coes,
      dsimp [finsupp.map_domain],

    end },
  inv :=
  { app := λ α s, s.sum multiset.repeat,
    naturality' := λ α β f, funext $ λ s,
      show (s.map_domain f).sum multiset.repeat = (s.sum multiset.repeat).map f,
      from finsupp.induction s rfl $ λ x n s hsx hn ih, begin
        rw [finsupp.map_domain_add, finsupp.sum_add_index, finsupp.map_domain_single, finsupp.sum_single_index,
            finsupp.sum_add_index, finsupp.sum_single_index, multiset.map_add, multiset.map_repeat, ih],
        { refl }, { intros, refl }, { intros, rw multiset.repeat_add },
        { refl }, { intros, refl }, { intros, rw multiset.repeat_add }
      end },
  hom_inv_id' := nat_trans.ext $ λ α, funext $ λ s,
    show (s.map $ λ x, finsupp.single x 1).sum.sum multiset.repeat = s,
    from multiset.induction_on s rfl $ λ a s ih, begin
      rw [multiset.map_cons, multiset.sum_cons, finsupp.sum_add_index, finsupp.sum_single_index, multiset.repeat_one, ih, multiset.cons_add, zero_add],
      { refl }, { intros, refl }, { intros, rw multiset.repeat_add }
    end,
  inv_hom_id' := nat_trans.ext $ λ α, funext $ λ s,
    show ((s.sum multiset.repeat).map $ λ x, finsupp.single x 1).sum = s,
    from finsupp.induction s rfl $ λ y n s hsy hn ih, begin
      rw [finsupp.sum_add_index, finsupp.sum_single_index, multiset.map_add, multiset.sum_add, ih, multiset.map_repeat],
      { congr' 1, clear hn, induction n with n ih,
        { rw [finsupp.single_zero, multiset.repeat_zero, multiset.sum_zero] },
        { rw [multiset.repeat_succ, multiset.sum_cons, ih, ← nat.one_add, finsupp.single_add] } },
      { refl }, { intros, refl }, { intros, rw multiset.repeat_add }
    end }

#exit
import data.num.basic
set_option profiler true
namespace nat

def fib : ℕ → ℕ
|     0 := 1
|     1 := 1
| (n+2) := fib n + fib (n+1)

def fib2 : ℕ → ℕ × ℕ
|     0 := (1, 0)
| (n+1) := let x := fib2 n in (x.1 + x.2, x.1)

def fib3 : ℕ → ℕ × ℕ
|     0 := (1, 0)
| (n+1) := ((fib3 n).1 + (fib3 n).2, (fib3 n).1)

def fib4 : ℕ → ℕ × ℕ
|     0 := (1, 0)
| (n+1) :=
  match fib4 n with
  | (x, y) := (x + y, x)
  end

#eval fib3 10
#eval fib4 100000
#eval fib2 100000
end nat

namespace num

def fib : ℕ → num
|     0 := 1
|     1 := 1
| (n+2) := fib n + fib (n+1)

def fib2 : ℕ → num × num
|     0 := (1, 0)
| (n+1) := let x := fib2 n in
  (x.1 + x.2, x.1)

def fib3 : ℕ → num × num
|     0 := (1, 0)
| (n+1) := ((fib3 n).1 + (fib3 n).2, (fib3 n).1)

def fib4 : ℕ → num × num
|     0 := (1, 0)
| (n+1) :=
  match fib4 n with
  | (x, y) := (x + y, x)
  end
--#reduce fib2 30
#reduce fib2 20
#reduce fib3 20
#reduce fib4 22

end num

set_option profiler true

-- #reduce fib 40

#eval fib3 100000

#exit
import data.nat.basic
open nat
theorem even_ne_odd {n m} : 2 * n ≠ 2 * m + 1 :=
mt (congr_arg (%2)) (by rw [add_comm, add_mul_mod_self_left, mul_mod_right]; exact dec_trivial)
#print even_ne_odd
#exit
import logic.function tactic
open monad

section

inductive p : Prop
| mk : p → p

example : ¬ p := λ h, by induction h; assumption

parameters {m : Type → Type} [monad m] [is_lawful_monad m]

inductive mem : Π {α : Type}, α → m α → Prop
| pure : ∀ {α : Type} (a : α), mem a (pure a)
| join : ∀ {α : Type} (a : α) (b : m α) (c : m (m α)), mem a b → mem b c →
  mem a (monad.join c)

parameters (mem2 : Π {α : Type}, α → m α → Prop)
  (mem2_pure : ∀ {α : Type} (a b : α), mem2 a (pure b) ↔ a = b)
  (mem2_bind : Π {α : Type} (a : α) (c : m (m α)),
    mem2 a (join c) ↔ ∃ b : m α, mem2 a b ∧ mem2 b c)

example (mem2 : Π {α : Type}, α → m α → Prop)
  (mem2_pure : ∀ {α : Type} {a b : α}, mem2 a (pure b) ↔ a = b)
  (mem2_join : Π {α : Type} (a : α) (c : m (m α)),
    mem2 a (join c) ↔ ∃ b : m α, mem2 a b ∧ mem2 b c)
  {α : Type} {a : α} (b : m α) (h : mem a b) : mem2 a b :=
by induction h; simp *; tauto

end

section

parameters {m : Type → Type} [monad m] [is_lawful_monad m]

inductive mem : Π {α : Type}, α → m α → Prop
| pure : ∀ {α : Type} (a : α), mem a (pure a)
| join : ∀ {α : Type} (a : α) (b : m α) (c : m (m α)), mem a b → mem b c →
  mem a (monad.join c)

parameters (mem2 : Π {α : Type}, α → m α → Prop)
  (mem2_pure : ∀ {α : Type} (a b : α), mem2 a (pure b) ↔ a = b)
  (mem2_bind : Π {α : Type} (a : α) (c : m (m α)),
    mem2 a (join c) ↔ ∃ b : m α, mem2 a b ∧ mem2 b c)

example (mem2 : Π {α : Type}, α → m α → Prop)
  (mem2_pure : ∀ {α : Type} {a b : α}, mem2 a (pure b) ↔ a = b)
  (mem2_join : Π {α : Type} (a : α) (c : m (m α)),
    mem2 a (join c) ↔ ∃ b : m α, mem2 a b ∧ mem2 b c)
  {α : Type} {a : α} (b : m α) (h : mem a b) : mem2 a b :=
by induction h; simp *; tauto

end

#exit
import data.matrix data.equiv.algebra

def one_by_one_equiv (one R : Type*) [unique one] [ring R] : matrix one one R ≃ R :=
{ to_fun := λ M, M (default _) (default _),
  inv_fun := λ x _ _, x,
  left_inv := λ _, matrix.ext
    (λ i j, by rw [unique.eq_default i, unique.eq_default j]),
  right_inv := λ _, rfl }

lemma one_by_one_equiv.is_ring_hom (one R : Type*) [unique one] [ring R] :
  is_ring_hom (one_by_one_equiv one R) :=
{ map_one := rfl,
  map_add := λ _ _, rfl,
  map_mul := λ _ _, by dsimp [one_by_one_equiv, matrix.mul]; simp }

def one_by_one_ring_equiv (one R : Type*) [unique one] [ring R] : matrix one one R ≃r R :=
{ hom := one_by_one_equiv.is_ring_hom one R,
  ..one_by_one_equiv one R }

import data.finset

#check @finset.sup

#exit
import measure_theory.giry_monad
universe u

variables {α : Type u} {β : Type u}
open nat

example {n : ℕ} : n ≤ n * n :=
begin
induction n_eq : n with m IH,
all_goals {
  have : 0 ≤ n, from n.zero_le
},
{ simp },
{ sorry }
end

lemma rubbish (n m : ℕ) (h : n = m) (hm : m ≠ 1) : n = 0 ∨ n > m :=
begin
  induction n,
  { left, refl },
  { -- case nat.succ
    -- m : ℕ,
    -- hm : m ≠ 1,
    -- n_n : ℕ,
    -- n_ih : n_n = m → n_n = 0 ∨ n_n > m,
    -- h : succ n_n = m
    -- ⊢ succ n_n = 0 ∨ succ n_n > m
    have : n_n = 0 ∨ n_n > m, from sorry,
    cases this,
    subst this, exfalso,
    exact hm h.symm,
    exact or.inr (lt_succ_of_lt this) }
end

example : false := absurd (rubbish 2 2) dec_trivial

open measure_theory measure_theory.measure

lemma inl_measurable_bind_ret [measurable_space α] [measurable_space β] (ν : measure β) :
  measurable (λ (x : α), bind ν (λ y, dirac (x, y))) :=
begin





end

#print measure.join

lemma inl_measurable_bind_ret' [measurable_space α] [measurable_space β] (w : measure β) :
  measurable (λ (x : α), bind w (λ y, dirac (x, y))) :=
have ∀ x : α, measurable (@prod.mk α β x),
  from λ x, measurable_prod_mk measurable_const measurable_id,
begin
  dsimp [measure.bind],
  conv in (map _ _) { rw [← measure.map_map measurable_dirac (this x)] },
  refine measurable_join.comp _,
  refine measurable.comp _ _,
  { refine measurable_map _ measurable_dirac },
  { sorry }




end

#exit


import data.equiv.encodable data.fintype

def f : bool → bool → bool
| tt tt := ff
| _ _   := tt
#print as_true
local notation `dec_trivial'` := of_as_true trivial

example : (∀ x y, f x y = f y x) ∧
  ¬(∀ x y z, f x (f y z) = f (f x y) z) := dec_trivial'

#eval ((finset.univ : finset (bool → bool → bool)).filter
  (λ f : bool → bool → bool, (∀ x y, f x y = f y x) ∧
  ¬(∀ x y z, f x (f y z) = f (f x y) z))).1.unquot.nth_le 0
  sorry ff ff


#exit
import data.finsupp order.complete_lattice algebra.ordered_group

namespace finsupp
open lattice
variables {σ : Type*} {α : Type*} [decidable_eq σ]

instance [preorder α] [has_zero α] : preorder (σ →₀ α) :=
{ le := λ f g, ∀ s, f s ≤ g s,
  le_refl := λ f s, le_refl _,
  le_trans := λ f g h Hfg Hgh s, le_trans (Hfg s) (Hgh s) }

instance [partial_order α] [has_zero α] : partial_order (σ →₀ α) :=
{ le_antisymm := λ f g hfg hgf, finsupp.ext $ λ s, le_antisymm (hfg s) (hgf s),
  .. finsupp.preorder }

instance [canonically_ordered_monoid α] : order_bot (σ →₀ α) :=
{ bot := 0,
  bot_le := λ f s, zero_le _,
  .. finsupp.partial_order }

def finsupp.of_pfun {α β : Type*} [has_zero β] [decidable_eq α] [decidable_eq β]
  (s : finset α) (f : Πa ∈ s, β) : α →₀ β :=
{ to_fun := λ a, if h : a ∈ s then f a h else 0,
  support := s.filter (λ a, ∃ h : a ∈ s, f a h ≠ 0),
    mem_support_to_fun := begin intros,
      simp only [finset.mem_def.symm, finset.mem_filter],
      split_ifs;
      split; {tauto <|> finish}
    end,  }

def downset [preorder α] (a : α) := {x | x ≤ a}
#print finsupp
lemma nat_downset (f : σ →₀ ℕ) : finset (σ →₀ ℕ) :=
(f.support.pi (λ s, finset.range (f s))).map
  ⟨_, _⟩

lemma nat_downset_eq_downset (f : σ →₀ ℕ) :
  (↑(nat_downset f) : set (σ →₀ ℕ)) = downset f := sorry

end finsupp
#exit
def r : ℕ → ℕ → Prop := classical.some (show ∃ r : ℕ → ℕ → Prop,
  equivalence r ∧ ∀ a c b d,
  r a b → r c d → r (a + c) (b + d), from ⟨(=), ⟨eq.refl, λ _ _, eq.symm, λ _ _ _, eq.trans⟩,
    by intros; simp *⟩)

instance X_setoid : setoid ℕ := ⟨r, (classical.some_spec r._proof_1).1⟩

def X : Type := quotient ⟨r, (classical.some_spec r._proof_1).1⟩


--computable
def add : X → X → X := λ a b, quotient.lift_on₂ a b
  (λ a b, ⟦a + b⟧)
  (λ a b c d hab hcd,
    quotient.sound $ (classical.some_spec r._proof_1).2 _ _ _ _ hab hcd)

#exit
import logic.basic tactic data.finset data.complex.basic data.polynomial
#print option.bind

lemma Z : has_sizeof (ℕ → ℕ) := by apply_instance
#eval sizeof ([] : list Type)
#eval sizeof (0 : polynomial (polynomial ℚ))
set_option pp.all true
#print Z

#print (infer_instance : )

#eval list.sizeof [@id ℕ]
#reduce λ α : Type, has_sizeof.sizeof α

inductive list2 : Type
| nil : list2
| cons : ℕ → ℕ → list2 → list2

#eval sizeof list2.nil

example {α: ℕ → Type u} (x y: ℕ) (a: α (x+y)) (b: α (y+x)) (h: a == b): true := begin
  -- i want (h: a = b)
  -- rw [nat.add_comm] at a, -- h still depends on old (a: α (x+y)) :<
  -- have h: a = b := eq_of_heq h, -- fail

  rw [nat.add_comm] at a,
  intros a b h,
  have h: a = b := eq_of_heq h, -- good

  trivial,
end

example (X Y : Type) (f : X → Y) (hf : function.bijective f) : ∃ g : Y → X, true :=
⟨λ y, hf _, trivial⟩

#exit

import data.polynomial



#print finset.prod_sum

set_option pp.proofs true
#print eq.drec
open polynomial
#eval ((finset.range 9).sum (λ n, (X : polynomial ℕ) ^ n)) ^ 5

#eval let k := 2 in ((k + 1) * (k + 2) * (k + 3) * (k + 4)) / nat.fact 4

#eval nat.choose 3 4

#exit
import algebra.char_p
#print classical.em
#print rel.comp
set_option pp.implicit true
set_option pp.notation false


lemma X : (⟨bool, tt⟩ : Σ α : Type, α) ≠ ⟨bool, ff⟩ :=
λ h, by cases h


#print X
#exit

import topology.opens

open topological_space continuous

def opens.what_is_this_called {X : Type*} [topological_space X]
  {U V : opens X} : opens V :=
U.comap

def well_ordering_rel {α : Type*} : α → α → Prop :=
classical.some well_ordering_thm

instance {α : Type*} : is_well_order α well_ordering_rel :=
classical.some_spec well_ordering_thm

local attribute [instance] classical.dec

noncomputable example {M : Type u → Type u} [monad M]
  {α β : Type u} (f : β → M α) : M (β → α) :=
let g : β → M (β → α) := λ i : β, (do x ← f i, return (λ _, x)) in
if h : nonempty β then g (classical.choice h) else return (λ i : β, false.elim (h ⟨i⟩))

example {M : Type u → Type u} [monad M] {α β : Type u} : (β → M α) → M (β → α) :=
let r := @well_ordering_rel β in
have h : Π a : β, ({x // r x a} → M α) → M ({x // r x a} → α),
  from well_founded.fix (show well_founded r, from sorry)
    (λ a ih f, do g ← ih a _ _, _),
begin



end

#print monad


#print is_lawful_monad
#print vector.traverse
import data.nat.basic tactic.ring

lemma silly (n d : ℕ) :  2 * (2 ^ n * d + 2 ^ n * 1) - 2 * 1 + 1 =
  2 ^ n * 2 * 1 + 2 ^ n * 2 * d - 1 :=
begin
  rw [mul_one 2, bit0, ← nat.sub_sub, nat.sub_add_cancel];
  ring,


end


#exit

noncomputable theory

open set function continuous

section homotopy

variables {X : Type*} [topological_space X]
variables {Y : Type*} [topological_space Y]
variables {Z : Type*} [topological_space Z]

lemma Union_inter_subset {α ι : Type*} {s t : ι → set α} :
  (⋃ i, (s i ∩ t i)) ⊆ (⋃ i, s i) ∩ (⋃ i, t i) :=
by finish [set.subset_def]

lemma Inter_union_subset {α ι : Type*} {s t : ι → set α} :
  (⋂ i, s i) ∪ (⋂ i, t i) ⊆ (⋂ i, (s i ∪ t i)) :=
by finish [set.subset_def]

local attribute [instance]classical.dec
/- pasting or gluing lemma: if a continuous function is continuous on finitely many
  closed subsets, it is continuous on the Union -/
theorem continuous_on_Union_of_closed {ι : Type*} [fintype ι]
  {s : ι → set X} (hs : ∀ i, is_closed (s i)) {f : X → Y}
  (h : ∀ i, continuous_on f (s i)) : continuous_on f (⋃ i, s i) :=
begin
  simp only [continuous_on_iff, mem_Union, exists_imp_distrib] at *,
  assume x i hi t ht hfxt,
  have h' : ∃ v : Π i, x ∈ s i → set X, ∀ i hi,
    is_open (v i hi) ∧ x ∈ v i hi ∧ v i hi ∩ s i ⊆ f ⁻¹' t,
  { simpa only [classical.skolem] using λ i hi, h i x hi t ht hfxt },
  cases h' with v hv,
  use ⋂ (i : ι), (⋂ (hi : x ∈ s i), v i hi) ∩ (⋂ (hi : x ∉ s i), -s i),
  refine ⟨is_open_Inter (λ j, is_open_inter
      (is_open_Inter_prop (λ _, (hv _ _).1))
      (is_open_Inter_prop (λ _, hs _))),
    mem_Inter.2 (λ j, mem_inter (mem_Inter.2 (λ _, (hv _ _).2.1)) (mem_Inter.2 id)),
    _⟩,
  assume y hy,
  simp only [mem_Inter, mem_inter_eq] at hy,
  cases mem_Union.1 hy.2 with j hyj,
  have hxj : x ∈ s j, from classical.by_contradiction (λ hxj, (hy.1 j).2 hxj hyj),
  exact (hv j hxj).2.2 ⟨(hy.1 j).1 _, hyj⟩
end

theorem continuous_on_Union_of_open {ι : Sort*}
  {s : ι → set X} (hs : ∀ i, is_open (s i)) {f : X → Y}
  (h : ∀ i, continuous_on f (s i)) : continuous_on f (⋃ i, s i) :=
begin
  simp only [continuous_on_iff, mem_Union, exists_imp_distrib] at *,
  assume x i hi t ht hfxt,
  have h' : ∃ v : Π i, x ∈ s i → set X, ∀ i hi,
    is_open (v i hi) ∧ x ∈ v i hi ∧ v i hi ∩ s i ⊆ f ⁻¹' t,
  { simpa only [classical.skolem] using λ i hi, h i x hi t ht hfxt },
  cases h' with v hv,
  use v i hi ∩ s i,
  use is_open_inter (hv _ _).1 (hs i),
  use mem_inter (hv _ _).2.1 hi,
  use subset.trans (inter_subset_left _ _) (hv i hi).2.2
end

lemma Inter_cond {α : Type*} {s t : set α} : (⋂ (i : bool), cond i t s) = s ∩ t :=
@Union_cond

lemma continuous_on_union_of_closed {s t : set X} (hsc : is_closed s)
  (htc : is_closed t) {f : X → Y} (hsf : continuous_on f s)
  (htf : continuous_on f t) : continuous_on f (s ∪ t) :=
by rw [← Union_cond]; exact continuous_on_Union_of_closed
  (λ i, bool.cases_on i hsc htc) (λ i, bool.cases_on i hsf htf)

lemma continuous_on_union_of_open {s t : set X} (hsc : is_open s)
  (htc : is_open t) {f : X → Y} (hsf : continuous_on f s)
  (htf : continuous_on f t) : continuous_on f (s ∪ t) :=
by rw [← Union_cond]; exact continuous_on_Union_of_open
  (λ i, bool.cases_on i hsc htc) (λ i, bool.cases_on i hsf htf)

#exit
import data.rat.denumerable
open encodable function lattice

namespace nat.subtype

variables {s : set ℕ} [decidable_pred s] [infinite s]

lemma exists_succ (x : s) : ∃ n, x.1 + n + 1 ∈ s :=
classical.by_contradiction $ λ h,
have ∀ (a : ℕ) (ha : a ∈ s), a < x.val.succ,
  from λ a ha, lt_of_not_ge (λ hax, h ⟨a - (x.1 + 1),
    by rwa [add_right_comm, nat.add_sub_cancel' hax]⟩),
infinite.not_fintype
  ⟨(((multiset.range x.1.succ).filter (∈ s)).pmap
      (λ (y : ℕ) (hy : y ∈ s), subtype.mk y hy)
      (by simp [-multiset.range_succ])).to_finset,
    by simpa [subtype.ext, multiset.mem_filter, -multiset.range_succ]⟩

def succ (x : s) : s :=
have h : ∃ m, x.1 + m + 1 ∈ s, from exists_succ x,
⟨x.1 + nat.find h + 1, nat.find_spec h⟩

lemma succ_le_of_lt {x y : s} (h : y < x) : succ y ≤ x :=
have hx : ∃ m, y.1 + m + 1 ∈ s, from exists_succ _,
let ⟨k, hk⟩ := nat.exists_eq_add_of_lt h in
have nat.find hx ≤ k, from nat.find_min' _ (hk ▸ x.2),
show y.1 + nat.find hx + 1 ≤ x.1,
by rw hk; exact add_le_add_right (add_le_add_left this _) _

lemma le_succ_of_forall_lt_le {x y : s} (h : ∀ z < x, z ≤ y) : x ≤ succ y :=
have hx : ∃ m, y.1 + m + 1 ∈ s, from exists_succ _,
show x.1 ≤ y.1 + nat.find hx + 1,
from le_of_not_gt $ λ hxy,
have y.1 + nat.find hx + 1 ≤ y.1 := h ⟨_, nat.find_spec hx⟩ hxy,
not_lt_of_le this $
  calc y.1 ≤ y.1 + nat.find hx : le_add_of_nonneg_right (nat.zero_le _)
  ... < y.1 + nat.find hx + 1 : nat.lt_succ_self _

lemma lt_succ_self (x : s) :  x < succ x :=
calc x.1 ≤ x.1 + _ : le_add_right (le_refl _)
... < succ x : nat.lt_succ_self (x.1 + _)

def of_nat (s : set ℕ) [decidable_pred s] [infinite s] : ℕ → s
| 0     := ⊥
| (n+1) := succ (of_nat n)

lemma of_nat_strict_mono : strict_mono (of_nat s) :=
nat.strict_mono_of_lt_succ (λ a, by rw of_nat; exact lt_succ_self _)

open list

lemma of_nat_surjective_aux : ∀ {x : ℕ} (hx : x ∈ s), ∃ n, of_nat s n = ⟨x, hx⟩
| x := λ hx, let t : list s := ((list.range x).filter (λ y, y ∈ s)).pmap
  (λ (y : ℕ) (hy : y ∈ s), ⟨y, hy⟩) (by simp) in
have hmt : ∀ {y : s}, y ∈ t ↔ y < ⟨x, hx⟩,
  by simp [list.mem_filter, subtype.ext, t]; intros; refl,
if ht : t = [] then ⟨0, le_antisymm (@bot_le s _ _)
  (le_of_not_gt (λ h, list.not_mem_nil ⊥ $
    by rw [← ht, hmt]; exact h))⟩
else by letI : inhabited s := ⟨⊥⟩;
  exact have wf : (maximum t).1 < x, by simpa [hmt] using list.mem_maximum ht,
  let ⟨a, ha⟩ := of_nat_surjective_aux (list.maximum t).2 in
  ⟨a + 1, le_antisymm
    (by rw of_nat; exact succ_le_of_lt (by rw ha; exact wf)) $
    by rw of_nat; exact le_succ_of_forall_lt_le
      (λ z hz, by rw ha; exact list.le_maximum_of_mem (hmt.2 hz))⟩

lemma of_nat_surjective : surjective (of_nat s) :=
λ ⟨x, hx⟩, of_nat_surjective_aux hx

def denumerable (s : set ℕ) [decidable_pred s] [infinite s] : denumerable s :=
have li : left_inverse (of_nat s) (λ x : s, nat.find (of_nat_surjective x)),
  from λ x, nat.find_spec (of_nat_surjective x),
denumerable.of_equiv ℕ
{ to_fun := λ x, nat.find (of_nat_surjective x),
  inv_fun := of_nat s,
  left_inv := li,
  right_inv := right_inverse_of_injective_of_left_inverse
    (strict_mono.injective of_nat_strict_mono) li }

end nat.subtype

variables {α : Type*} [encodable α] [decidable_eq α]

def decidable_range_encode : decidable_pred (set.range (@encode α _)) :=
λ x, decidable_of_iff (option.is_some (decode2 α x))
  ⟨λ h, ⟨option.get h, by rw [← decode2_is_partial_inv (option.get h), option.some_get]⟩,
  λ ⟨n, hn⟩, by rw [← hn, encodek2]; exact rfl⟩

variable [infinite α]

def demumerable_of_encodable_of_infinite : denumerable α :=
by letI := @decidable_range_encode α _ _;
  letI : infinite (set.range (@encode α _)) :=
    infinite.of_injective _ (equiv.set.range _ encode_injective).injective;
  letI := nat.subtype.denumerable (set.range (@encode α _)); exact
denumerable.of_equiv (set.range (@encode α _))
{ to_fun := _ }

#exit
import topology.instances.real

lemma bool_ne_nat : bool ≠ nat :=
begin


end

#print set.image_preimage_eq
instance z : topological_space Prop := by apply_instance
#print sierpinski_space
#print topological_space.generate_from
#print continuous_generated_from

example {α : Type*} [topological_space α] : continuous (eq : α → α → Prop) :=
continuous_pi (λ x, _)

example {α : Type*} [topological_space α] {s : α → Prop} :
  continuous s ↔ is_open s :=
⟨λ h, by convert h {true} (by simp); simp [eq_true, set.preimage, set_of],
  λ _, continuous_generated_from $ by simpa [set.preimage, eq_true, set_of]⟩

def foo : nat → Prop
| 0 := true
| (n+1) := (foo n) ∧ (foo n)

meta def mk_foo_expr : nat → expr
| 0 := `(trivial)
| (n+1) :=
  expr.app
    (expr.app
      (reflected.to_expr `(@and.intro (foo n) (foo n)))
      (mk_foo_expr n))
    (mk_foo_expr n)

open tactic

meta def show_foo : tactic unit :=
do `(foo %%nx) ← target,
   n ← eval_expr nat nx,
   exact (mk_foo_expr n)

set_option profiler true

lemma foo_200 : foo 500 :=
by show_foo

#print foo_200
#exit
import tactic category_theory.limits.types

def colimit_cocone {J Y : Type} {X : J → Type} (t : Π j : J, X j → Y)
  (h : ∀ {α : Type} (f g : Y → α), (∀ j x, f (t j x) = g (t j x)) → f = g) :
  ∀ y : Y, ∃ j x, t j x = y :=
@eq.rec _ _ (λ P : Y → Prop, ∀ y, P y)
    (λ _, true.intro) _
    (@h Prop (λ _, true)
    (λ y, ∃ j x, t j x = y)
    (λ j x, propext ⟨λ _, ⟨j, x, eq.refl _⟩,
      λ _, true.intro⟩))
#print category_theory.functor.id
open category_theory

def fin_functor : functor ℕ Type :=
{ obj := fin,
  map := λ a b ⟨⟨h⟩⟩ i, ⟨i.1, lt_of_lt_of_le i.2 h⟩ }
#print functor.obj
def type_of {α : Sort*} (x : α) : Sort* := α
#reduce type_of (limits.types.colimit.{0} fin_functor).ι.app

example : sorry :=
begin
  have := @colimit_cocone ℕ _ _
    ((limits.types.colimit.{0} fin_functor).ι.app) begin

     end,

end

#print colimit_cocone
#reduce colimit_cocone
#reduce propext
#exit
import data.vector2

inductive expression : Type
| a {dim : ℕ} (v : fin dim → expression) /- omitted constraints on dim -/ : expression
| b : expression
open expression

#print expression.sizeof
#print vector.of_fn
def f (e : expression) : ℕ :=
expression.rec_on e
  (λ n idx f, 1 + (vector.of_fn f).1.sum)
  1

def f : expression -> ℕ
| (a idx) := 1 + ((vector.of_fn (λ x, idx x)).map f).1.sum

--using_well_founded {rel_tac := λ_ _, `[exact ⟨_, measure_wf (λ e, expression_size e)⟩] }

#exit

import data.rat.basic algebra.archimedean

lemma lt_of_mul_lt_mul_left' {α : Type*} [ordered_ring α]
  {a b c : α} (hc : c ≥ 0) (h : c * a < c * b) : a < b := sorry

lemma div_le_div {a b : ℤ} : ((a / b : ℤ) : ℚ) ≤ a / b :=
if hb : b = 0 then by simp [hb]
else
have hb0 : 0 < (b : ℚ), from nat.cast_pos.2 _,
le_of_mul_le_mul_left (@le_of_add_le_add_left ℚ _ (a % b : ℤ) _ _
  begin
    rw [← int.cast_mul, ← int.cast_add, int.mod_add_div,
      mul_div_cancel', add_comm],
    exact le_add_of_le_of_nonneg (le_refl _)
      (int.cast_nonneg.2 (int.mod_nonneg _ hb)),
  end)
hb0

lemma div_eq_rat_floor (n : ℤ) (d : ℕ) : n / d = ⌊(n : ℚ) / d⌋ :=
if h : d = 0 then by simp [h]
else
have hd0 : (d : ℚ) ≠ 0, by simpa,
have hd0' : 0 < (d : ℚ), from sorry,
le_antisymm
  (le_floor.2 _)
  (int.le_of_lt_add_one $ floor_lt.2 (lt_of_mul_lt_mul_left'
    (show (0 : ℚ) ≤ d, from nat.cast_nonneg _)
    (begin
        rw [mul_div_cancel' _ hd0, int.cast_add, add_comm, mul_add,
          int.cast_one, mul_one],
        conv {to_lhs, rw ← int.mod_add_div n d},
        simp,
        rw [← int.cast_coe_nat d, int.cast_lt],
        convert int.mod_lt _ (int.coe_nat_ne_zero.2 h),
        simp
      end)))


open nat

inductive le' (a : ℕ) : ℕ → Prop
| refl : le' a
| succ : ∀ b, le' b → le' (succ b)

infix ` ≤' `: 50 := le'

lemma le'_trans {a b c : ℕ} (hab : a ≤' b) (hbc : b ≤' c) : a ≤' c :=
le'.rec_on hbc hab (λ _ _, le'.succ _)

def lt' (a b : ℕ) : Prop :=
succ a ≤' b

infix ` <' `:50 := lt'

lemma le_of_lt' {a b : ℕ} (h : a <' b) : a ≤' b :=
le'.rec_on h (le'.succ _ (le'.refl _)) (λ _ _, le'.succ _)

lemma b (a b c : ℕ) (hab : a <' b) (hbc : b <' c) : a <' c :=
le'_trans hab (le_of_lt' hbc)

#reduce b 3 4 5 (le'.refl _) (le'.refl _)

#exit
import algebra.module
import group_theory.group_action
import linear_algebra.basic -- this import breaks the commented lines at the end of the file

class group_module (G M : Type) [monoid G] [add_comm_group M]
  extends mul_action G M :=
(smul_add  : ∀ (g : G) (m₁ m₂ : M), g • (m₁ + m₂) = g • m₁ + g • m₂)

attribute [simp] group_module.smul_add

namespace fixed_points
open mul_action
variables {G M : Type}
variables [monoid G] [add_comm_group M]
variable [group_module G M]

lemma add_mem (x y : M) (hx : x ∈ fixed_points G M) (hy : y ∈ fixed_points G M) :
  x + y ∈ fixed_points G M :=
begin
  intro g,
  simp only [mem_stabilizer_iff, group_module.smul_add, mem_fixed_points] at *,
  rw [hx, hy],
end

end fixed_points

class representation (G R M : Type) [monoid G] [ring R] [add_comm_group M] [module R M]
  extends group_module G M :=
(smul_comm : ∀ (g : G) (r : R) (m : M), g • (r • m) = r • (g • m))

--namespace representation
--open mul_action linear_map


variables {G R M : Type}
variables [group G] [ring R] [ring M] [module R M] [representation G R M]

set_option trace.class_instances true
--set_option class_

lemma smul_mem_fixed_points (r : R) (m : M) (hm : m ∈ mul_action.fixed_points G M) :
  (r • m : M) = sorry :=
begin
  simp only [mem_fixed_points] at *,
  intro g,
  rw [smul_comm, hm],
end
end representation


import data.equiv.basic order.zorn
open function set zorn

variables {α : Type*} {β : Type*} [nonempty β]

instance m : partial_order (α → β) :=
{ le := λ x y, range x ⊆ range y ∧ ∀ a, y a ∈ range x → y a = x a,
  le_trans := λ x y z hxy hyz, ⟨subset.trans hxy.1 hyz.1,
    λ a ha, begin
      rw [hyz.2 a (hxy.1 ha), hxy.2 a],
      rwa [← hyz.2 a (hxy.1 ha)]
    end⟩,
  le_refl := λ _, ⟨subset.refl _, λ _ _, rfl⟩,
  le_antisymm := λ x y hxy hyx,
    by simp only [subset.antisymm hxy.1 hyx.1] at *;
    exact funext (λ a, (hxy.2 _ ⟨a, rfl⟩).symm) }


example : ∃ f : α → β, ∀ g, f ≤ g → g ≤ f :=
zorn _
  (λ _ _ _, le_trans)

example {α β : Type*} [nonempty β] : {f : α → β // injective f ∨ surjective f} :=
let r :

begin


end


#exit
import data.list.basic

#print has_to
#print galois_insterion
@[derive decidable_eq] inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml
infixr ` →' `:50 := imp -- right associative

prefix `¬' `:51 := fml.not

inductive prf : fml → Type
| axk {p q} : prf (p →' q →' p)
| axs {p q r} : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX {p q} : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

instance (p): has_sizeof (prf p) := by apply_instance

open prf

meta def length {f : fml} (t : prf f) : ℕ :=
prf.rec_on t (λ _ _, 1) (λ _ _ _, 1) (λ _ _, 1) (λ _ _ _ _, (+))

instance (p q : fml) : has_coe_to_fun (prf (p →' q)) :=
{ F := λ x, prf p → prf q,
  coe := λ x y, mp y x }

lemma imp_self' (p : fml) : prf (p →' p) :=
mp (@axk p p) (mp axk axs)

lemma imp_comm {p q r : fml} (h : prf (p →' q →' r)) : prf (q →' p →' r) :=
mp axk (mp (mp (mp h axs) axk) (@axs _ (p →' q) _))

lemma imp_of_true (p : fml) {q : fml} (h : prf q) : prf (p →' q) :=
mp h axk

namespace prf
prefix `⊢ `:30 := prf

def mp' {p q} (h1 : ⊢ p →' q) (h2 : ⊢ p) : ⊢ q := mp h2 h1
def a1i {p q} : ⊢ p → ⊢ q →' p := mp' axk
def a2i {p q r} : ⊢ p →' q →' r → ⊢ (p →' q) →' p →' r := mp' axs
def con4i {p q} : ⊢ ¬' p →' ¬' q → ⊢ q →' p := mp' axX
def mpd {p q r} (h : ⊢ p →' q →' r) : ⊢ p →' q → ⊢ p →' r := mp' (a2i h)
def syl {p q r} (h1 : ⊢ p →' q) (h2 : ⊢ q →' r) : ⊢ p →' r := mpd (a1i h2) h1
def id {p} : ⊢ p →' p := mpd axk (@axk p p)
def a1d {p q r} (h : ⊢ p →' q) : ⊢ p →' r →' q := syl h axk
def com12 {p q r} (h : ⊢ p →' q →' r) : ⊢ q →' p →' r := syl (a1d id) (a2i h)
def con4d {p q r} (h : ⊢ p →' ¬' q →' ¬' r) : ⊢ p →' r →' q := syl h axX
def absurd {p q} : ⊢ ¬' p →' p →' q := con4d axk
def imidm {p q} (h : ⊢ p →' p →' q) : ⊢ p →' q := mpd h id
def contra {p} : ⊢ (¬' p →' p) →' p := imidm (con4d (a2i absurd))
def notnot2 {p} : ⊢ ¬' ¬' p →' p := syl absurd contra
def mpdd {p q r s} (h : ⊢ p →' q →' r →' s) : ⊢ p →' q →' r → ⊢ p →' q →' s := mpd (syl h axs)
def syld {p q r s} (h1 : ⊢ p →' q →' r) (h2 : ⊢ p →' r →' s) : ⊢ p →' q →' s := mpdd (a1d h2) h1
def con2d {p q r} (h1 : ⊢ p →' q →' ¬' r) : ⊢ p →' r →' ¬' q := con4d (syld (a1i notnot2) h1)
def con2i {p q} (h1 : ⊢ p →' ¬' q) : ⊢ q →' ¬' p := con4i (syl notnot2 h1)
def notnot1 {p} : ��� p →' ¬' ¬' p := con2i id

#reduce notnot2


infixr ` →' `:50 := imp -- right associative

prefix `¬' `:51 := fml.not

def p_of_p (p : fml) : prf (p →' p) :=
mp (@axk p p) (mp axk axs)

inductive consequence (G : list fml) : fml → Type
| axk (p q) : consequence (p →' q →' p)
| axs (p q r) : consequence $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axn (p q) : consequence $ ((¬'q) →' (¬'p)) ���' p →' q
| mp (p q) : consequence p → consequence (p →' q) → consequence q
| of_G (g ∈ G) : consequence g

def consequence_of_thm (f : fml) (H : prf f) (G : list fml) : consequence G f :=
begin
  induction H,
  exact consequence.axk G H_p H_q,
  exact consequence.axs G H_p H_q H_r,
  exact consequence.axn G H_p H_q,
  exact consequence.mp H_p H_q H_ih_a H_ih_a_1,
end

def thm_of_consequence_null (f : fml) (H : consequence [] f) : prf f :=
begin
  induction H,
  exact @axk H_p H_q,
  exact @axs H_p H_q H_r,
  exact @axX H_p H_q,
  exact mp H_ih_a H_ih_a_1,
  exact false.elim (list.not_mem_nil H_g H_H),
end

def deduction (G : list fml) (p q : fml) (H : consequence (p :: G) q) : consequence G (p →' q) :=
begin
  induction H,
  have H1 := consequence.axk G H_p H_q,
  have H2 := consequence.axk G (H_p →' H_q →' H_p) p,
  exact consequence.mp _ _ H1 H2,
  have H6 := consequence.axs G H_p H_q H_r,
  have H7 := consequence.axk G ((H_p →' H_q →' H_r) →' (H_p →' H_q) →' H_p →' H_r) p,
  exact consequence.mp _ _ H6 H7,
  have H8 := consequence.axn G H_p H_q,
  have H9 := consequence.axk G (((¬' H_q) →' ¬' H_p) →' H_p →' H_q) p,
  exact consequence.mp _ _ H8 H9,
  have H3 := consequence.axs G p H_p H_q,
  have H4 := consequence.mp _ _ H_ih_a_1 H3,
  exact consequence.mp _ _ H_ih_a H4,
  rw list.mem_cons_iff at H_H,
  exact if h : H_g ∈ G then
  begin
    have H51 := consequence.of_G H_g h,
    have H52 := consequence.axk G H_g p,
    exact consequence.mp _ _ H51 H52,
  end else
  begin
    have h := H_H.resolve_right h,
    rw h,
    exact consequence_of_thm _ (p_of_p p) G,
  end
end

def part1 (p : fml) : consequence [¬' (¬' p)] p :=
begin
  have H1 := consequence.axk [¬' (¬' p)] p p,
  have H2 := consequence.axk [¬' (¬' p)] (¬' (¬' p)) (¬' (¬' (p →' p →' p))),
  have H3 := consequence.of_G (¬' (¬' p)) (list.mem_singleton.2 rfl),
  have H4 := consequence.mp _ _ H3 H2,
  have H5 := consequence.axn [¬' (¬' p)] (¬' p) (¬' (p →' p →' p)),
  have H6 := consequence.mp _ _ H4 H5,
  have H7 := consequence.axn [¬' (¬' p)] (p →' p →' p) p,
  have H8 := consequence.mp _ _ H6 H7,
  exact consequence.mp _ _ H1 H8,
end

def p_of_not_not_p (p : fml) : prf ((¬' (¬' p)) →' p) :=
begin
  have H1 := deduction [] (¬' (¬' p)) p,

  have H2 := H1 (part1 p),
  exact thm_of_consequence_null ((¬' (¬' p)) →' p) H2,
end

#reduce p_of_not_not_p
#reduce @notnot2

theorem not_not_p_of_p (p : fml) : prf (p →' (¬' (¬' p))) :=
begin
  have H1 := prf.axs p (¬' (¬' p)),
  have H2 := p_of_not_not_p (¬' p),
  exact thm.mp H2 H1,
end
set_option pp.implicit true
#reduce not_not_p_of_p

#exit
@[derive decidable_eq] inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:40 := fml.not

inductive prf : fml → Type
| axk (p q) : prf (p →' q →' p)
| axs (p q r) : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX (p q) : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

#print prf.rec

open prf

/-
-- example usage:
lemma p_of_p_of_p_of_q (p q : fml) : prf $ (p →' q) →' (p →' p) :=
begin
  apply mp (p →' q →' p) ((p →' q) →' p →' p) (axk p q),
  exact axs p q p
end
-/

def is_not : fml → Prop :=
λ f, ∃ g : fml, f = ¬' g

#print prf.rec_on
theorem Q6b (f : fml) (p : prf f) : is_not f → false :=
begin
  induction p,
  {admit},
  {admit},
  {admit},
  {
    clear p_ih_a_1,
    }


end

#print Q6b

theorem Q6b : ∀ p : fml, ¬(prf $ p →' ¬' ¬' p) :=
begin
  cases p,


end


#exit

import data.fintype

section

@[derive decidable_eq] inductive cbool
| t : cbool
| f : cbool
| neither : cbool
open cbool

instance : fintype cbool := ⟨{t,f,neither}, λ x, by cases x; simp⟩

variables (imp : cbool → cbool → cbool) (n : cbool → cbool)
  (a1 : ∀ p q, imp p (imp q p) = t)
  (a2 : ∀ p q, imp (imp (n q) (n p)) (imp p q) = t)
  (a3 : ∀ p q r, imp (imp p (imp q r)) (imp (imp p q) (imp p r)) = t)
include a1 a2 a3

set_option class.instance_max_depth 50

-- example : ∀ p, imp p (n (n p)) = t :=
-- by revert imp n; exact dec_trivial



#exit
import measure_theory.measure_space topology.metric_space.emetric_space

noncomputable lemma F {α β : Sort*} : ((α → β) → α) → α :=
classical.choice $ (classical.em (nonempty α)).elim
  (λ ⟨a⟩, ⟨λ _, a⟩)
  (λ h, ⟨λ f, false.elim (h ⟨f (λ a, false.elim (h ⟨a⟩))⟩)⟩)

#reduce F

def X {α : Type*} [add_monoid α] {p : α → Prop} [is_add_submonoid p]: add_monoid (subtype p) :=
subtype.add_monoid

instance add_monoid_integrable' [is_add_submonoid (ball (0 : ℝ) ⊤)]:
  add_monoid (subtype (ball (0 : ℝ) ⊤)) := X

#exit
import measure_theory.measurable_space

example {α : Type*} [add_monoid α] (p : set α): add_monoid (subtype p) := by apply_instance
#print topological_add_group
#eval ((univ : finset (perm (fin 7))).filter (λ x, sign x = 1 ∧ order_of x = 6)).card


import data.polynomial tactic.omega

open polynomial
set_option trace.simplify.rewrite true
example (x : ℤ) : x ^ 2 + x = x + x * x :=
by ring

example (a b c d e f : ℤ) (ha : a ≤ 2) (hb : c ≥ b - e) (hf : 5 * f - 2 * c = 9 * b - 7 * e)
  (hd : d + 3 ≤ 7 + e) : d + 3 ≤ 7 + e := by omega


open mv_polynomial
set_option trace.simplify.rewrite true
lemma z : (X () : mv_polynomial unit ℤ) ^ 2 = X () * X () :=
begin
  ring,

end
#print z

#exit
import tactic.omega

example (a b c : ℕ) (hab : 20 * a + 2 * b = 10 * b + c + 10 * c + a)
  (ha : a < 10) (hb : b < 10) (hc : c < 10) : a = b ∧ b = c :=
by omega

example : ∀ {a : ℕ} (ha : a < 10) {b : ℕ} (hb : b < 10) {c : ℕ} (hc : c < 10)
  (hab : 20 * a + 2 * b = 10 * b + c + 10 * c + a), a = b ∧ b = c :=
by omega


#exit
import data.equiv.algebra

variables {α : Type*} {β : Type*} [add_monoid β] (e : α ≃ β)

instance foo : add_monoid α := equiv.add_monoid e

--import tactic.omega
#exit
example (p q : ℕ → Prop) (h : p = q) (x : subtype p) :
  (eq.rec_on h x : subtype q) = ⟨x.1, h ▸ x.2⟩ :=
begin
  cases x, subst h,

end

def X : Type := ℤ

set_option trace.class_instances true
instance : comm_ring X := by apply_instance

lemma whatever (a b : ℕ) : a + b = 1 ↔ (a = 1 ∧ b = 0) ∨ (b = 1 ∧ a = 0) := by omega
#print whatever

example : 1000000 * 1000000 = 1000000000000 := by norm_num

lemma h (a b n : ℤ) : a + b - b + n = a + n := by simp

example : (1 : ℤ) + 2 - 2 + 3 = 1 + 3 := h 1 2 3

example : default Prop := trivial

inductive nat2
| zero : nat2
| succ : nat2 → nat2

#print nat2.zero
#print nat2.succ
#print nat2.rec

def add (a b : nat2) : nat2 :=
nat2.rec a (λ c, nat2.succ) b

example : ∀ (b : ℕ), b = b := by omega
example : ∃ (a : ℕ), a = 0 := by omega
example :

#print z

example : (∀ p q r : Prop, ((p ↔ q) ↔ r) ↔ (p ↔ (q ↔ r))) → ∀ p, p ∨ ¬p :=
λ h p, ((h (p ∨ ¬p) false false).mp
  ⟨λ h, h.mp (or.inr (λ hp, h.mp (or.inl hp))), false.elim⟩).mpr iff.rfl

noncomputable def step_fun : ℝ → ℝ := λ x, if x ≤ ξ then 1 else 0

lemma discont_at_step : ¬ (continuous_at step_fun ξ) :=
begin
  unfold continuous_at,
  -- our goal:
  -- ⊢ ¬filter.tendsto step_fun (nhds ξ) (nhds (step_fun ξ))
  rw metric.tendsto_nhds_nhds,
  push_neg,
  -- goal
  -- ∃ (ε : ℝ), ε > 0 ∧ ∀ (δ : ℝ), δ > 0 → (∃ {x : ℝ},
  -- dist x ξ < δ ∧ ε ≤ dist (step_fun x) (step_fun ξ))
  use 1,
  refine ⟨by norm_num, _⟩,
  assume δ δ0,
  use ξ + δ / 2,
  split,
  { simp [real.dist_eq, abs_of_nonneg (le_of_lt (half_pos δ0)), half_lt_self δ0] },
  { have : ¬ ξ + δ / 2 ≤ ξ, from not_le_of_gt ((lt_add_iff_pos_right _).2 (half_pos δ0)),
    simp [real.dist_eq, step_fun, le_refl, this] }
end


#exit
import data.set.basic data.finset

variables {α : Type*} {A B : set α}

theorem Q8: (A \ B) ∪ (B \ A) = (A ∪ B) \ (A ∩ B) :=
set.ext $ λ x, ⟨λ h, h.elim (λ h, ⟨or.inl h.1, mt and.right h.2⟩)
    (λ h, ⟨or.inr h.1, mt and.left h.2⟩),
  λ h, h.1.elim (λ hA, or.inl ⟨hA, λ hB, h.2 ⟨hA, hB⟩⟩)
    (λ hB, or.inr ⟨hB, λ hA, h.2 ⟨hA, hB⟩⟩)⟩

lemma f : has_sub (set α) := by apply_instance

#print f

#print axioms Q8
#print axioms

#exit
import set_theory.cardinal tactic.norm_num

def list_to_nat : list bool → nat
| [] := 0
| (ff :: l) := 3 ^ (list_to_nat l) + 1
| (tt :: l) := 3 ^ (list_to_nat l) + 2

lemma list_to_nat_injective : function.injective list_to_nat
| [] [] h := rfl
| (a::l) [] h := by cases a; exact nat.no_confusion h
| [] (a::l) h := by cases a; exact nat.no_confusion h
| (a::l₁) (b::l₂) h := begin
  cases a; cases b;
  dunfold list_to_nat at h,
  simp [pow_left_inj] at h,

end


noncomputable def list_unit_equiv_list_bool : list unit ≃ list bool :=
classical.choice $ quotient.exact $
show cardinal.mk (list unit) = cardinal.mk (list bool),
  begin
   rw [cardinal.mk_list_eq_sum_pow, cardinal.mk_list_eq_sum_pow],
   apply le_antisymm,
   { refine cardinal.sum_le_sum _ _ (λ _, cardinal.power_le_power_right $
       ⟨⟨λ _, tt, λ _ _ _, subsingleton.elim _ _⟩⟩), },
   { simp, }

end


#print nat.to_digits
#print nat.to_digi
def bool_to_unit : l :=


lemma injective_unit_to_bool : function.injective unit_to_bool
| [] [] h := rfl
| (x::l) [] h := by cases x; exact absurd h (list.cons_ne_nil _ _)
| [] (x::l) h := by cases x; exact absurd h (λ h, list.cons_ne_nil _ _ h.symm)
| (tt::l₁) (tt::l₂) h := begin
  unfold unit_to_bool at h,
  simp at h,
  rw injective_unit_to_bool h
end
| (ff::l₁) (ff::l₂) h := begin
  unfold unit_to_bool at h,
  simp at h,
  rw injective_unit_to_bool h
end
| (tt::l₁) (ff::l₂) h := begin
  unfold unit_to_bool at h,
  simp at h,
  rw ← unit_to_bool at h,
  have := injective_unit_to_bool h,
end

example : list unit ≃ list bool :=
#exit
import data.fintype
--set_option pp.all true
lemma fin_injective {n m : ℕ} (h : fin n = fin m) : n = m :=
have e : fin n ≃ fin m, by rw h,
by rw [← fintype.card_fin n, fintype.card_congr e, fintype.card_fin]

lemma h : ∀ n, su

#print (show ∀ n, (subsingleton (fin n)), by apply_instance)
instance gjh (α : Type*) : subsingleton (fintype α) :=
⟨λ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩, by congr⟩

#print fin_injective
#print axioms fintype.card_fin
#print axioms fin_injective
#exit
import data.real.basic data.set.intervals topology.basic analysis.complex.exponential
local attribute [instance] classical.prop_decidable

open real

noncomputable def fake_abs (x : ℝ) : ℝ := if x ≤ 0 then -x else x

noncomputable def fake_abs' : ℝ → ℝ := λ x, if x ≤ 0 then -x else x

#print prefix fake_abs.equations._eqn_1

#print prefix fake_abs'.equations._eqn_1

#exit
import set_theory.ordinal
universe u
open function lattice
theorem schroeder_bernstein {α β : Type*} {f : α → β} {g : β → α}
  (hf : injective f) (hg : injective g) : ∃h:α→β, bijective h :=
let s : set α := lfp $ λs, - (g '' - (f '' s)) in
have hs : s = - (g '' - (f '' s)) :=
begin
  dsimp [s, lfp, lattice.Inf, has_Inf.Inf,
    complete_lattice.Inf, set.mem_set_of_eq,
    set.image, set.compl, has_le.le,
    preorder.le, partial_order.le, order_bot.le,
    bounded_lattice.le, complete_lattice.le, has_neg.neg,
    boolean_algebra.neg, complete_boolean_algebra.neg,
    set.subset_def],
  simp only [not_exists, classical.not_forall, not_and, set.ext_iff,
    set.mem_set_of_eq], intro,
  split; finish

  --simp at hs,

end, sorry

open function

lemma injective_of_increasing {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) [is_trichotomous α r]
  [is_irrefl β s] (f : α → β) (hf : ∀{x y}, r x y → s (f x) (f y)) : injective f :=
begin
  intros x y hxy,
  rcases trichotomous_of r x y with h | h | h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this,
  exact h,
  have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this
end

def well_order {α : Type*} : α → α → Prop := classical.some (@well_ordering_thm α)

def wf {α : Type*} : has_well_founded α :=
⟨well_order, (classical.some_spec (@well_ordering_thm α)).2⟩

open cardinal

local attribute [instance] wf
variable {α : Type u}
local infix ` ≺ `:50 := well_order

instance is_well_order_wf : is_well_order _ ((≺) : α → α → Prop) :=
classical.some_spec (@well_ordering_thm α)

noncomputable def to_cardinal {α : Type u} : α → cardinal.{u}
| a := cardinal.succ (@cardinal.sup.{u u} {y : α // y ≺ a}
   (λ y, have y.1 ≺ a, from y.2, to_cardinal y.1))
using_well_founded {dec_tac := tactic.assumption }

local attribute [instance] classical.dec
#print cardinal
lemma to_cardinal_increasing : ∀ {x y : α} (h : x ≺ y), to_cardinal x < to_cardinal y
| a b hab :=
have ha' : a = (show subtype (≺ b), from ⟨a, hab⟩).1, by simp,
begin
  conv {to_rhs, rw [to_cardinal], congr, congr, funext, rw to_cardinal },
  rw [to_cardinal, cardinal.lt_succ],
  have ha' : a = (show subtype (≺ b), from ⟨a, hab⟩).1, by simp,
  rw ha',
  exact le_sup _ _
end

lemma to_cardinal_injective : function.injective (@to_cardinal α) :=
injective_of_increasing (≺) (<) _ (λ _ _, to_cardinal_increasing)

def to_Type : α → Type u :=
quotient.out ∘ to_cardinal

#print to_Type

lemma injective_to_Type : function.injective (@to_Type α) :=
function.injective_comp (λ x y h, by convert congr_arg cardinal.mk h; simp)
  to_cardinal_injective

lemma Type_gt : (Type u ↪ α) → false :=
λ ⟨f, h⟩, cantor_injective (f ∘ @to_Type (set α))
  (function.injective_comp h injective_to_Type)

lemma universe_strict_mono : (Type (u+1) ↪ Type u) → false := Type_gt

lemma universe_strict_mono' : Type u ↪ Type (u+1) :=
⟨_, injective_to_Type⟩
--#print embedding.trans
example : cardinal.lift.{(u+1) (u+2)} (cardinal.mk (Type u)) <
  cardinal.mk (Type (u+1)) :=
lt_of_not_ge (λ ⟨f⟩, universe_strict_mono
  (f.trans ⟨ulift.down, λ ⟨_⟩ ⟨_⟩ h, congr_arg _ h⟩))

-- lemma injective_of_increasing {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) [is_trichotomous α r]
--   [is_irrefl β s] (f : α → β) (hf : ∀{x y}, r x y → s (f x) (f y)) : injective f :=
-- begin
--   intros x y hxy,
--   rcases trichotomous_of r x y with h | h | h,
--   have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this,
--   exact h,
--   have := hf h, rw hxy at this, exfalso, exact irrefl_of s (f y) this
-- end

-- def well_order {α : Type*} : α → α → Prop := classical.some (@well_ordering_thm α)

-- def wf {α : Type*} : has_well_founded α :=
-- ⟨well_order, (classical.some_spec (@well_ordering_thm α)).2⟩

-- open cardinal

-- local attribute [instance] wf
-- variable {α : Type u}
-- local infix ` ≺ `:50 := well_order

-- instance is_well_order_wf : is_well_order _ ((≺) : α → α → Prop) :=
-- classical.some_spec (@well_ordering_thm α)

-- noncomputable def to_cardinal {α : Type u} : α → cardinal.{u}
-- | a := cardinal.succ (@cardinal.sup.{u u} {y : α // y ≺ a}
--    (λ y, have y.1 ≺ a, from y.2, to_cardinal y.1))
-- using_well_founded {dec_tac := tactic.assumption }

-- local attribute [instance] classical.dec

-- lemma to_cardinal_increasing : ∀ {x y : α} (h : x ≺ y), to_cardinal x < to_cardinal y
-- | a b hab :=
-- have ha' : a = (show subtype (≺ b), from ⟨a, hab⟩).1, by simp,
-- begin
--   conv {to_rhs, rw [to_cardinal], congr, congr, funext, rw to_cardinal },
--   rw [to_cardinal, cardinal.lt_succ],
--   have ha' : a = (show subtype (≺ b), from ⟨a, hab⟩).1, by simp,
--   rw ha',
--   exact le_sup _ _
-- end

-- lemma to_cardinal_injective : function.injective (@to_cardinal α) :=
-- injective_of_increasing (≺) (<) _ (λ _ _, to_cardinal_increasing)

-- def to_Type : α → Type u :=
-- quotient.out ∘ to_cardinal

-- lemma injective_to_Type : function.injective (@to_Type α) :=
-- function.injective_comp (λ x y h, by convert congr_arg cardinal.mk h; simp)
--   to_cardinal_injective

-- lemma Type_gt : (Type u ↪ α) → false :=
-- λ ⟨f, h⟩, cantor_injective (f ∘ @to_Type (set α))
--   (function.injective_comp h injective_to_Type)

-- lemma universe_strict_mono : (Type (u+1) ↪ Type u) → false := Type_gt


#exit
inductive foo: ℕ → ℕ → Type
def foo_fn (n m: ℕ): Type := foo n m → foo n m

inductive is_foo_fn
  : Π {n m: ℕ}, foo_fn n m → Type
| IsFooEta:
  Π {n m: ℕ} {f: foo_fn n m},
  is_foo_fn f
→ is_foo_fn (λ M, f M)
open is_foo_fn

def ext: -- equation compiler failed to prove equation lemma (
 -- workaround: disable lemma generation using `set_option eqn_compiler.lemmas false`)
    Π {n m: ℕ}
      {f: foo_fn n m},
    is_foo_fn f
  → Σ f': foo_fn n m, is_foo_fn f'
| _ _ _ (IsFooEta f) :=
  ⟨_, IsFooEta (ext f).snd⟩

set_option trace.simp_lemmas
def ext2: -- equation compiler failed to prove equation lemma
--(workaround: disable lemma generation using `set_option eqn_compiler.lemmas false`)
    Π {m n : ℕ}
      {f: foo_fn n m},
    is_foo_fn f
  → Σ f': foo_fn n m, is_foo_fn f'
| _ _ _ (IsFooEta f) :=
  ⟨_, IsFooEta (ext2 f).snd⟩

#print ext2._main

example : ∀ (n m : ℕ) (z : foo_fn n m) (f : is_foo_fn z),
  ext2 (IsFooEta f) = ⟨λ (M : foo n m), (ext2 f).fst M, IsFooEta ((ext2 f).snd)⟩ :=
λ _ _ _ _, rfl

#print ext.equations._eqn_1

#exit
import data.finset data.fintype

variables {α : Type*} {β : Type*}
@[instance] lemma nat.cast_coe : has_coe nat string := sorry
local attribute [-instance] nat.cast_coe

def embeddings [decidable_eq α] [decidable_eq β] :
  Π (l : list α), list β → list (Π a : α, a ∈ l → β)
| []     l   := [λ _ h, false.elim h]
| (a::l) []  := []
| (a::l₁) l₂ := (embeddings l₁ l₂).bind
  (λ f, (l₂.filter (λ b, ∀ a h, f a h ≠ b)).map
    (λ b a' ha', if h : a' = a then b else _))

#eval (embeddings [1,2,3,4,5] [1,2,3,4,5]).length
#eval 5^5
lemma card_embeddings :

#exit
import tactic

#print prod.lex

example {α : Type*} [preorder α] {x y : α × α}: prod.lex ((<) : α → α → Prop) (≤) x y
  ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2) :=
begin
  split,
  { assume h,
    { induction h;simp * at * } },
  { assume h,
    cases x, cases y,
    cases h,
    refine prod.lex.left _ _ _ h,
    dsimp at h,
    rw h.1,
    refine prod.lex.right _ _ h.2 }

end
example {α : Type*} {β : α → Type*} [preorder α] [Π a : α, preorder (β a)]
  {x y : psigma β} : psigma.lex (<) (λ a : α, @has_le.le (β a) _) x y
  ↔ x.1 < y.1 ∨ ∃ p : x.1 = y.1, x.2 ≤ by convert y.2 :=
begin
  split,
  { assume h,
    induction h; simp [*, eq.mpr] at * },
  { assume h, cases x, cases y,
    cases h,
    refine psigma.lex.left _ _ _ h,
    cases h,
    dsimp at h_w,
    subst h_w,
    refine psigma.lex.right _ _ h_h }
end

#exit
import tactic.interactive

def f {α : Type*} [decidable_eq α] (x y : α) : bool := x = y

local attribute [instance, priority 0] classical.prop_decidable

example {α : Type*} {P : Prop} {x y : α} (hxy : f x y = tt)
  (hP : f x y = tt → P) : P :=
by tauto!

#exit
import topology.metric_space.basic

def inclusion {α : Type*} {s t : set α} (h : s ⊆ t) : s → t :=
λ x : s, (⟨x, h x.2⟩ : t)

@[simp] lemma inclusion_self {α : Type*} {s : set α} (h : s ⊆ s) (x : s) :
  inclusion h x = x := by cases x; refl

@[simp] lemma inclusion_inclusion {α : Type*} {s t u : set α} (hst : s ⊆ t) (htu : t ⊆ u)
  (x : s) : inclusion htu (inclusion hst x) = inclusion (set.subset.trans hst htu) x :=
by cases x; refl

lemma inclusion_injective {α : Type*} {s t : set α} (h : s ⊆ t) :
  function.injective (inclusion h)
| ⟨_, _⟩ ⟨_, _⟩ := subtype.ext.2 ∘ subtype.ext.1

example {α : Type*} [topological_space α] (s t : set α) (h : s ⊆ t) :
  continuous (inclusion h) :=
continuous_subtype_mk

#exit
import algebra.associated

#print irreducible
]


end⟩

#print prime

#exit
example : ∃ h : 1 = 1, true := dec_trivial

#exit
import topology.basic data.set.intervals analysis.exponential
open real set

-- Give a handle on the set [0,1] ⊂ ℝ
def unit_interval := (Icc (0:ℝ) 1)
-- Define an identity function on the subtype corresponding to this set
def restricted_id := function.restrict (λ (x:ℝ), x) unit_interval

-- show that restricted_id is continuous
lemma cont_restricted_id : continuous restricted_id :=
begin
intro,
intro,
apply continuous_subtype_val _,
exact a,
end
-- main idea: "getting the value of the subtype" unifies with "restricted_id"

-- now show that the identity function (on ℝ) is continuous on the unit interval
lemma continuous_on_unit_interval_id : continuous_on (λ (x:ℝ), x) unit_interval :=
begin
rw [continuous_on_iff_continuous_restrict],
exact cont_restricted_id,
end

-- This breaks for 1/x, obviously.
-- First of all, we can't just use subtype.val, since that won't unify.
-- To get some hope that it will go through thing, let's start over with the interval (0,1].
def ounit_interval := (Ioc (0:ℝ) 1)

noncomputable def restricted_inv := function.restrict (λ (x:ℝ), 1/x) ounit_interval

lemma cont_restricted_inv : continuous restricted_inv :=
begin
  unfold restricted_inv function.restrict,
  simp only [one_div_eq_inv],
  exact continuous_inv (λ a, (ne_of_lt a.2.1).symm) continuous_subtype_val,
end
#print real.uniform_continuous_inv
#exit

open nat
#eval gcd (gcd (61 ^ 610 + 1) (61 ^ 671 - 1) ^ 671 + 1)
  (gcd (61 ^ 610 + 1) (61 ^ 671 - 1) ^ 610 - 1) % 10

example : gcd (gcd (61 ^ 610 + 1) (61 ^ 671 - 1) ^ 671 + 1)
  (gcd (61 ^ 610 + 1) (61 ^ 671 - 1) ^ 610 - 1) % 10 = 3 :=
begin


end

#exit
import tactic.ring data.real.basic algebra.module
example (x : ℝ) : x=2 → 2+x=x+2 := begin intro h, ring, end -- works
example (x : ℝ) : x=2 → 2*x=x*2 := begin intro h, ring, end -- works
example (x y : ℝ) : (x - y) ^ 3 = x^3 - 3 * x^2 * y + 3 * x * y^2 - y^3 := by ring

#print semimodule
constant r : ℕ → ℕ → Prop
notation a ` ♥ `:50 b :50:= r b a
infix ` ♠ ` : 50 := r
#print notation ♥
example (a b : ℕ) : a ♥ b :=
begin
/-
1 goal
a b : ℕ
⊢ b ♠ a
-/
end


#exit
import tactic.norm_num data.zmod.basic



#print X

example : ∀ (x y z : zmod 9), x^3 + y^3 + z^3 ≠ 4 := dec_trivial


#exit
import analysis.normed_space.basic

variable {Β : Type*}

namespace hidden

@[simp] lemma norm_mul [normed_field-eq B] (a b : Β) : ∥a * b∥ = ∥a∥ * ∥b∥ :=
normed_field.norm_mul a b

instance normed_field.is_monoid_hom_norm [normed_field α] : is_monoid_hom (norm : α → ℝ) :=
⟨norm_one, norm_mul⟩

@[simp] lemma norm_pow [normed_field α] : ∀ (a : α) (n : ℕ), ∥a^n∥ = ∥a∥^n :=
is_monoid_hom.map_pow norm

end hidden

#exit
import tactic.norm_num

def FP_step : ℕ × ℕ → ℕ × ℕ :=
 λ ⟨a,b⟩, ⟨b,(a + b) % 89⟩

def FP : ℕ → ℕ × ℕ
| 0 := ⟨0,1⟩
| (n + 1) := FP_step (FP n)

def F (n : ℕ) : ℕ := (FP n).fst

lemma FP_succ {n a b c : ℕ}
  (h : FP n = (a, b)) (h2 : (a + b) % 89 = c) : FP (nat.succ n) = (b, c) :=
by rw [← h2, FP, h]; refl
set_option pp.max_steps 1000000000
set_option pp.max_depth 1000000000

lemma L : F 44 = 0 := begin
  have : FP 0 = (0, 1) := rfl,
  iterate 44 { replace := FP_succ this (by norm_num; refl) },
  exact congr_arg prod.fst this
end

lemma zero_eq_one : 0 = @has_zero.zero ℕ ⟨1⟩ :=
begin
  refl,
end

#print L

#exit
--import data.zmod.basic

lemma double_neg_em : (∀ p, ¬¬p → p) ↔ (∀ p, p ∨ ¬p) :=
⟨λ dneg p, dneg (p ∨ ¬ p) (λ h, h (or.inr (h ∘ or.inl))),
λ em p hneg, (em p).elim id (λ h, (hneg h).elim)⟩
#print or.assoc
lemma z : (∀ {α : Type} {p : α → Prop}, (∀ x, p x) ↔ ∄ x, ¬ p x) → ∀ (P : Prop), P ∨ ¬ P :=
λ h P, (@h unit (λ _, P ∨ ¬ P)).2 (λ ⟨_, h⟩, h (or.inr (h ∘ or.inl))) ()
#print axioms z

lemma y : (7 + 8) + 5 = 7 + (8 + 5) :=
add_assoc 7 8 5
#print axioms nat.mul_assoc
#reduce y

example : 0 = @has_zero.zero ℕ ⟨1⟩ :=
begin
  refl,

end

example : (⊥ : ℕ) = @lattice.has_bot.bot ℕ ⟨1⟩ :=
begin
  refl,

end


lemma b {m n : ℕ} : (m * n) % n = 0 :=
nat.mul_mod_left _ _


lemma iff_assoc {p q r : Prop} : p ↔ (q ↔ r) ↔ (p ↔ q ↔ r) := by tauto!

#print iff_assoc

lemma eq_assoc {p q r : Prop} : p = (q = r) = (p = q = r) :=
by simpa [iff_iff_eq] using iff.assoc

#print iff_assoc
#reduce iff.assoc

example {p q : Prop} : (p ↔ p ∧ q) ↔ (p → q) :=
by split; intros; simp * at *

#exit
import data.real.basic

example : (2 : ℝ) ≤ ((((2 - (157 / 50 / 2 ^ (4 + 1)) ^ 2) ^ 2 - 2) ^ 2 - 2) ^ 2 - 2) ^ 2 :=
begin
  rw (show 4 + 1 = 5, from rfl),
  rw (show (2 : ℝ) ^ 5 = 32, by norm_num),
  rw (show (157 : ℝ) / 50 / 32 = 157 / 1600, by norm_num),
  rw (show ((157 : ℝ) / 1600) ^ 2 = 24649 / 2560000, by norm_num),
  rw (show (2 : ℝ) - 24649 / 2560000 = 5095351/2560000, by norm_num),
  rw (show ((5095351 : ℝ) /2560000) ^ 2 = 25962601813201/6553600000000, by norm_num),
  -- let's try skipping steps
  rw (show ((((25962601813201 : ℝ) / 6553600000000 - 2) ^ 2 - 2) ^ 2 - 2) ^ 2 =
    6806775565993596917798714352237438749189222725565123913061124308255143227446400872965401873904861225601/3402823669209384634633746074317682114560000000000000000000000000000000000000000000000000000000000000000,
    by norm_num),
  -- worked!
  -- ⊢ 2 ≤
  --  6806775565993596917798714352237438749189222725565123913061124308255143227446400872965401873904861225601 /
  --    3402823669209384634633746074317682114560000000000000000000000000000000000000000000000000000000000000000
  rw le_div_iff,
  { norm_num },
  { norm_num }
  -- ⊢ 0 < 3402823669209384634633746074317682114560000000000000000000000000000000000000000000000000000000000000000

end


import algebra.big_operators data.int.basic

open finset nat
variables {α : Type*} [semiring α]
--set_option trace.simplify.rewrite true

lemma nat.sub_right_inj {a b c : ℕ} (h₁ : c ≤ a) (h₂ : c ≤ b) : a - c = b - c ↔ a = b :=
by rw [nat.sub_eq_iff_eq_add h₁, nat.sub_add_cancel h₂]

lemma lemma1 {x y z : ℕ → α} (n : ℕ) : (range (n + 1)).sum
  (λ i, (range (i + 1)).sum (λ j, x j * y (i - j)) * z (n - i)) =
  (range (n + 1)).sum (λ i, x i * (range (n - i + 1)).sum (λ j, y j * z (n - i - j))) :=
begin
  induction n,
  { simp [mul_assoc] },
  { simp [*, mul_assoc, @range_succ (succ n_n)] at * }
end

#print imp_congr_ctx
#print lemma1

#exit
import algebra.group data.equiv.basic

variables {α : Type*} {β : Type*}

structure monoid_equiv (α β : Type*) [monoid α] [monoid β] extends α ≃ β :=
(mul_hom : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

infix ` ≃ₘ ` : 50 := monoid_equiv

instance sfklkj [monoid α] [monoid β] (f : α ≃ₘ β) : is_monoid_hom f.to_fun :=
{ map_mul := f.mul_hom,
  map_one := calc f.to_equiv.to_fun 1
    = f.to_equiv.to_fun 1 * f.to_equiv.to_fun (f.to_equiv.inv_fun 1) :
      by rw [f.to_equiv.right_inv, mul_one]
    ... = 1 : by rw [← f.mul_hom, one_mul, f.to_equiv.right_inv] }

#exit
import data.multiset


open nat

def S : multiset ℕ := quot.mk _ [1,2]

def T : multiset ℕ := quot.mk _ [2,1]

lemma S_eq_T : S = T := quot.sound (list.perm.swap _ _ _)

def X (m : multiset ℕ) : Type := {n : ℕ // n ∈ m}

def n : X S := ⟨1, dec_trivial⟩

def n' : X T := eq.rec_on S_eq_T n
set_option pp.proofs true
#reduce n'

def id' (n : ℕ) : ℕ := pred (1 + n)

lemma id'_eq_id : id' = id := funext $ λ _, by rw [id', add_comm]; refl

def Y (f : ℕ → ℕ) : Type := {n : ℕ // f n = n}

def m : Y id := ⟨0, rfl⟩

def m' : Y id' := eq.rec_on id'_eq_id.symm m
set_option pp.proofs true
#reduce m'

import topology.metric_space.basic tactic.find
open filter
universes u v
variables {ι : Type u} {α : ι → Type v} [fintype ι] [∀ i, metric_space (α i)]

#print function.inv_fun

lemma g : lattice.complete_lattice Prop := by apply_instance
#print lattice.complete_lattice_Prop
lemma h :
  (⨅ (ε : ℝ) (h : ε > 0), principal {p : (Π i, α i) × (Π i, α i) | dist p.1 p.2 < ε} =
  ⨅ i : ι, filter.comap (λ a : (Π i, α i)×(Π i, α i), (a.1 i, a.2 i)) uniformity)
  =
  ∀ (ε : ℝ) (h : ε > 0), principal {p : (Π i, α i) × (Π i, α i) | dist p.1 p.2 < ε} =
  ⨅ i : ι, filter.comap (λ a : (Π i, α i)×(Π i, α i), (a.1 i, a.2 i)) uniformity :=
by simp [lattice.infi_Prop_eq]

#exit

--local attribute [semireducible] reflected
#print char.to_nat
#print string.to_nat
#eval "∅".front.to_nat

#eval (⟨11, dec_trivial⟩ : char)
#eval "∅".front.to_nat - "/".front.to_nat
#eval 8662 - 8192 - 256 - 128 - 64 - 16 - 4 - 2
#eval "/".front.to_nat

meta def f (n : ℕ) (e : expr): expr :=
`(nat.add %%e %%`(n))

def g : ℕ := by tactic.exact (f 5 `(1))
#print int
#eval g

def foo : bool → nat → bool
| tt 0     := ff
| tt m     := tt
| ff 0     := ff
| ff (m+1) := foo ff m

#print prefix foo
#print reflect
#eval foo tt 1


#exit
import topology.metric_space.basic
open nat
structure aux : Type 1 :=
(space  : Type)
(metric : metric_space space)

set_option eqn_compiler.zeta true

noncomputable def my_def (X : ℕ → Type) [m : ∀n, metric_space (X n)] : ∀n:ℕ, aux
| 0 :=
  { space := X 0,
    metric := by apply_instance }
| (succ n) :=
  { space := prod (my_def n).space (X n.succ),
    metric := @prod.metric_space_max _ _ (my_def n).metric _ }

#print prefix my_def
set_option pp.all true
#print my_def._main

example : ∀ (X : nat → Type) [m : Π (n : nat), metric_space.{0} (X n)] (n : nat),
  @eq.{2} aux (@my_def._main X m (nat.succ n))
    {space := prod.{0 0} ((@my_def._main X m n).space) (X (nat.succ n)),
     metric := @prod.metric_space_max.{0 0} ((@my_def._main X m n).space) (X (nat.succ n))
                 ((@my_def._main X m n).metric)
                 (m (nat.succ n))} :=
  λ _ _ _, by tactic.reflexivity tactic.transparency.all

example : ∀ (X : nat → Type) [m : Π (n : nat), metric_space.{0} (X n)] (n : nat),
  @eq.{2} aux {space := prod.{0 0} ((@my_def._main X m n).space) (X (nat.succ n)),
     metric := @prod.metric_space_max.{0 0} ((@my_def._main X m n).space) (X (nat.succ n))
                 ((@my_def._main X m n).metric)
                 (m (nat.succ n))}
{space := prod.{0 0} ((@my_def X m n).space) (X (nat.succ n)),
     metric := @prod.metric_space_max.{0 0} ((@my_def X m n).space) (X (nat.succ n))
     ((@my_def X m n).metric)
                 (m (nat.succ n))} := λ _ _ _, rfl
example : my_def = my_def._main := rfl

lemma b : ∀ (X : nat → Type) [m : Π (n : nat), metric_space.{0} (X n)] (n : nat),
  @eq.{2} aux
    {space := prod.{0 0} ((@my_def X m n).space) (X (nat.succ n)),
     metric := @prod.metric_space_max.{0 0} ((@my_def X m n).space) (X (nat.succ n))
     ((@my_def X m n).metric)
                 (m (nat.succ n))}
    (@my_def X m (nat.succ n))
  := λ _ _ _, by tactic.reflexivity tactic.transparency.all

example (X : ℕ → Type) [m : ∀n, metric_space (X n)] (n : ℕ) :
  my_def X (n+1) = ⟨(my_def X n).space × (X n.succ),
    @prod.metric_space_max.{0 0} _ _ (my_def X n).metric _⟩ :=
by refl

#print my_def._main
#exit
import tactic

class A (α : Type*) :=
(a : α)

class B (α : Type*) extends A α :=
(b : α)

class C (α : Type*) :=
(a : α)
(t : true)

instance C.to_A (α : Type*) [C α] : A α :=
{ ..show C α, by apply_instance }

instance B.to_C {α : Type*} [B α] : C α :=
{ t := trivial, .. show B α, by apply_instance }

def B.to_A' (α : Type*) [n : B α] : A α :=
A.mk (B.to_A α).a

def a' {α : Type*} [A α] := A.a α

example {α : Type*} [n : B α] (x : α) (h : @a' _ (B.to_A α) = x) : @a' _ (C.to_A α) = x :=
by rw h


namespace foo
open classical

local attribute [instance] classical.prop_decidable
@[derive decidable_eq] inductive value : Type

@[derive decidable_eq] structure foo :=
(bar : ℕ)

end foo

#exit
example {p : Prop} : (∀ q, (p → q) → q) → p :=
λ h, classical.by_contradiction (h false)


import logic.function data.quot data.set.basic
universe u
inductive tree_aux (α : Type u) : bool → Type u
| nil : tree_aux ff
| cons : α → tree_aux ff → tree_aux ff
| mk_tree : α → tree_aux ff → tree_aux tt


variables (α : Type*) (β : Type*) (γ : Type*) (δ : Type*)

open function

example {p q : Prop} (h : p → q) : ¬q → ¬p := (∘ h)

#check ((∘) ∘ (∘)) not eq
#reduce (λ (x : α → β) (y : δ → γ → α) (z : δ) (w : γ), ((∘) ∘ (∘)) x y z w)

def fun_setoid {α β} (f : α → β) : setoid α :=
{ r := (∘ f) ∘ eq ∘ f,
  iseqv := ⟨λ _, rfl, λ _ _, eq.symm, λ _ _ _, eq.trans⟩ }

#reduce (λ f : α → β, ((∘ f) ∘ eq ∘ f))

structure quotient_map (α β : Type*) :=
(to_fun : α → β)
(inv_fun : β → quotient (fun_setoid to_fun))
(right_inverse : right_inverse inv_fun
  (λ a : quotient (fun_setoid to_fun), quotient.lift_on' a to_fun (λ _ _, id)))

example {α : Type*} [s : setoid α] : quotient_map α (quotient s) :=
{ to_fun := quotient.mk,
  inv_fun := λ a, quotient.lift_on a (λ a, (quotient.mk' a : quotient (fun_setoid quotient.mk)))
    (λ a b h, quotient.sound' (quotient.sound h)),
  right_inverse := λ x, quotient.induction_on x (λ _, rfl) }



#exit
import topology.metric_space.isometry

variables {X : Type*} {Y : Type*} [metric_space X] [metric_space Y] (i : X ≃ᵢ Y)
open metric

def jaih : bool := true

#print jaih
#print to_bool

#print (true : bool)

#exit
import logic.function

universes u v
axiom choice : Π (α : Sort u), nonempty (nonempty α → α)
∈
example : nonempty (Π {α : Sort u}, nonempty α → α) :=
let ⟨x⟩ := choice (Σ' α : Sort u, nonempty α) in
have _ := x _,
⟨_⟩
#reduce function.cantor_surjective
#exit
import topology.continuity
open set
variables {X : Type*} {Y : Type*} [topological_space X] [topological_space Y]
#print prod.topological_space
#print topological_space.generate_open
#reduce (@prod.topological_space X Y _ _).is_open
def prod_topology : topological_space (X × Y) :=
{ is_open := λ R, ∃ S : set (set (X × Y)), R = ⋃₀ S ∧
    ∀ s ∈ S, ∃ (U : set X) (hU : is_open U) (V : set Y) (hV : is_open V), s = set.prod U V,
  is_open_univ := sorry,
  is_open_inter := sorry,
  is_open_sUnion := sorry }
example : @prod_topology X Y _ _ = prod.topological_space := rfl
attribute [instance, priority 1000] prod_topology

example (U : set X) (V : set Y) : set.prod U V = prod.fst ⁻¹' U ∩ prod.snd ⁻¹' V := rfl
#print topolog
example {Z : Type*}[topological_space Z]
  (f : Z → X × Y) (hX : continuous (prod.fst ∘ f)) (hY : continuous (prod.snd ∘ f)) :
  continuous f :=
λ S ⟨T, hT⟩, begin
  rw [hT.1, preimage_sUnion],
  refine is_open_Union (λ s, is_open_Union (λ hs, _)),
  rcases hT.2 s hs with ⟨U, hU, V, hV, hUV⟩,
  rw hUV,
  show is_open (((prod.fst ∘ f)⁻¹' U) ∩ (prod.snd ∘ f)⁻¹' V),
  exact is_open_inter (hX _ hU) (hY _ hV)
end

example {X Y: Type*} [topological_space X] [topological_space Y]
  (f : X → Y) (hf : continuous f) (V : set Y) : is_closed V → is_closed (f ⁻¹' V) :=
hf _

#print set.prod
#print has_seq
example {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
  (f : Z → X × Y) (hX : continuous (prod.fst ∘ f)) (hY : continuous (prod.snd ∘ f)) :
  continuous f :=
λ S hS, begin
  rw is_open_prod_iff at hS,


end
#print g

#exit
import data.complex.exponential analysis.exponential algebra.field topology.algebra.topological_structures

open real

theorem continuous_cos_x_plus_x : continuous (λ x, cos x + x) :=
continuous_add real.continuous_cos continuous_id

theorem continuous_cos_x_plus_x' : continuous (λ x, cos x + x) :=
begin
 refine continuous_add _ _,
 exact continuous_cos,
 exact continuous_id,
end

namespace nzreal

def nzreal := {r : ℝ // r ≠ 0}
notation `ℝ*` := nzreal
constants nzc nzd : nzreal

-- one_ne_zero is zero_ne_one backwards
instance nzreal.one : has_one nzreal := ⟨⟨(1:ℝ), one_ne_zero⟩⟩

noncomputable instance nzreal.div : has_div nzreal :=
 ⟨λ q r, ⟨q.val / r.val, div_ne_zero q.property r.property⟩⟩

def nzreal_to_real (z : nzreal) : ℝ := subtype.val z
instance : has_lift nzreal real := ⟨nzreal_to_real⟩

class real.nzreal (r : ℝ) :=
(p : ℝ*)
(pf : r = ↑p)

-- idea is copied from data.real.nnreal
instance : has_coe ℝ* ℝ := ⟨subtype.val⟩

-- copy from Kevin Buzzard post on "computable division by non-zero real"
noncomputable instance : topological_space ℝ* := by unfold nzreal; apply_instance

end nzreal

-- almost the same as the proof for continuity of tangent
theorem continuous_1_over_x : continuous (λ (x : ℝ*), 1/x) :=
continuous_subtype_mk _ $ continuous_mul
  (continuous_subtype_val.comp continuous_const)
  (continuous_inv subtype.property
    (continuous_subtype_val.comp continuous_id))

#exit
import data.complex.basic

example {z : ℂ} :

#exit
import ring_theory.unique_factorization_domain

namespace hidden

constant α : Type

@[instance] constant I : integral_domain α

@[elab_as_eliminator] axiom induction_on_prime {P : α → Prop}
  (a : α) (h₁ : P 0) (h₂ : ∀ x : α, is_unit x → P x)
  (h₃ : ∀ a p : α, a ≠ 0 → prime p → P a → P (p * a)) : P a

local infix ` ~ᵤ ` : 50 := associated

#print associated

lemma factors_aux (a : α) : a ≠ 0 → ∃ s : multiset α, a ~ᵤ s.prod ∧ ∀ x ∈ s, irreducible x :=
induction_on_prime a (by simp)
  (λ x hx hx0, ⟨0, by simpa [associated_one_iff_is_unit]⟩)
  (λ a p ha0 hp ih hpa0, let ⟨s, hs₁, hs₂⟩ := ih ha0 in
    ⟨p :: s, by rw multiset.prod_cons;
      exact associated_mul_mul (associated.refl p) hs₁,
    λ x hx, (multiset.mem_cons.1 hx).elim (λ hxp, hxp.symm ▸ irreducible_of_prime hp) (hs₂ _)⟩)

@[simp] lemma mul_unit_dvd_iff {a b : α} {u : units α} : a * u ∣ b ↔ a ∣ b :=
⟨λ ⟨d, hd⟩, by simp [hd, mul_assoc], λ ⟨d, hd⟩, ⟨(u⁻¹ : units α) * d, by simp [mul_assoc, hd]⟩⟩

lemma dvd_iff_dvd_of_rel_left {a b c : α} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c :=
let ⟨u, hu⟩ := h in hu ▸ mul_unit_dvd_iff.symm

@[simp] lemma dvd_mul_unit_iff {a b : α} {u : units α} : a ∣ b * u ↔ a ∣ b :=
⟨λ ⟨d, hd⟩, ⟨d * (u⁻¹ : units α), by simp [(mul_assoc _ _ _).symm, hd.symm]⟩,
  λ h, dvd.trans h (by simp)⟩

lemma dvd_iff_dvd_of_rel_right {a b c : α} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c :=
let ⟨u, hu⟩ := h in hu ▸ dvd_mul_unit_iff.symm

lemma ne_zero_iff_of_associated {a b : α} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 :=
⟨λ ha, let ⟨u, hu⟩ := h in hu ▸ mul_ne_zero ha (units.ne_zero _),
  λ hb, let ⟨u, hu⟩ := h.symm in hu ▸ mul_ne_zero hb (units.ne_zero _)⟩



lemma irreducible_of_associated {p q : α} (h : irreducible p) :
  p ~ᵤ q → irreducible q :=
λ ⟨u, hu⟩, ⟨_, _⟩

lemma prime_of_irreducible {p : α} : irreducible p → prime p :=
induction_on_prime p (by simp) (λ p hp h, (h.1 hp).elim)
  (λ a p ha0 hp ih hpa, (hpa.2 p a rfl).elim (λ h, (hp.2.1 h).elim)
    (λ ⟨u, hu⟩, prime_of_associated hp ⟨u, hu ▸ rfl⟩))
#print multiset.prod
local attribute [instance] classical.dec

lemma multiset.dvd_prod {a : α} {s : multiset α} : a ∈ s → a ∣ s.prod :=
quotient.induction_on s (λ l a h, by simpa using list.dvd_prod h) a

lemma exists_associated_mem_of_dvd_prod {p : α} (hp : prime p) {s : multiset α} :
  (∀ r ∈ s, prime r) → p ∣ s.prod → ∃ q ∈ s, p ~ᵤ q :=
multiset.induction_on s (by simp [mt is_unit_iff_dvd_one.2 hp.2.1])
  (λ a s ih hs hps, begin
    rw [multiset.prod_cons] at hps,
    cases hp.2.2 _ _ hps with h h,
    { use [a, by simp],
      cases h with u hu,
      cases ((irreducible_of_prime (hs a (multiset.mem_cons.2
        (or.inl rfl)))).2 p u hu).resolve_left hp.2.1 with v hv,
      exact ⟨v, by simp [hu, hv]⟩ },
    { rcases ih (λ r hr, hs _ (multiset.mem_cons.2 (or.inr hr))) h with ⟨q, hq₁, hq₂⟩,
      exact ⟨q, multiset.mem_cons.2 (or.inr hq₁), hq₂⟩ }
  end)

lemma associated_mul_left_cancel {a b c d : α} (h : a * b ~ᵤ c * d) (h₁ : a ~ᵤ c)
  (ha : a ≠ 0) : b ~ᵤ d :=
let ⟨u, hu⟩ := h in let ⟨v, hv⟩ := associated.symm h₁ in
⟨u * (v : units α), (domain.mul_left_inj ha).1
  begin
    rw [← hv, mul_assoc c (v : α) d, mul_left_comm c, ← hu],
    simp [hv.symm, mul_assoc, mul_comm, mul_left_comm]
  end⟩

noncomputable instance : unique_factorization_domain α :=
{ factors := λ a, if ha : a = 0 then 0 else classical.some (factors_aux a ha),
  factors_prod := λ a ha, by rw dif_neg ha;
    exact associated.symm (classical.some_spec (factors_aux a ha)).1,
  irreducible_factors := λ a ha, by rw dif_neg ha;
    exact (classical.some_spec (factors_aux a ha)).2,
  unique := λ f, multiset.induction_on f
      (λ g _ hg h,
        multiset.rel_zero_left.2 $
          multiset.eq_zero_of_forall_not_mem (λ x hx,
            have is_unit g.prod, by simpa [associated_one_iff_is_unit] using h.symm,
            (hg x hx).1 (is_unit_iff_dvd_one.2 (dvd.trans (multiset.dvd_prod hx)
              (is_unit_iff_dvd_one.1 this)))))
      (λ p f ih g hf hg hfg,
        let ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod
          (prime_of_irreducible (hf p (by simp)))
          (λ q hq, prime_of_irreducible (hg _ hq)) $
            (dvd_iff_dvd_of_rel_right hfg).1
              (show p ∣ (p :: f).prod, by simp) in
        begin
          rw ← multiset.cons_erase hbg,
          exact multiset.rel.cons hb (ih (λ q hq, hf _ (by simp [hq]))
            (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))
            (associated_mul_left_cancel
              (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
            (nonzero_of_irreducible (hf p (by simp)))))
        end),
  ..I }

end hidden
#exit
/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Cast of characters:

`P`   : a polynomial functor
`W`   : its W-type
`M`   : its M-type
`F`   : a functor
`q`   : `qpf` data, representing `F` as a quotient of `P`

The main goal is to construct:

`fix`   : the initial algebra with structure map `F fix → fix`.
`cofix` : the final coalgebra with structure map `cofix → F cofix`

We also show that the composition of qpfs is a qpf, and that the quotient of a qpf
is a qpf.
-/
import tactic.interactive data.multiset
universe u

/-
Facts about the general quotient needed to construct final coalgebras.
-/




namespace quot

def factor {α : Type*} (r s: α → α → Prop) (h : ∀ x y, r x y → s x y) :
  quot r → quot s :=
quot.lift (quot.mk s) (λ x y rxy, quot.sound (h x y rxy))

def factor_mk_eq {α : Type*} (r s: α → α → Prop) (h : ∀ x y, r x y → s x y) :
  factor r s h ∘ quot.mk _= quot.mk _ := rfl

end quot

/-
A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P.apply α`.

An element of `P.apply α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/

structure pfunctor :=
(A : Type u) (B : A → Type u)

namespace pfunctor

variables (P : pfunctor) {α β : Type u}

-- TODO: generalize to psigma?
def apply (α : Type*) := Σ x : P.A, P.B x → α

def map {α β : Type*} (f : α → β) : P.apply α → P.apply β :=
λ ⟨a, g⟩, ⟨a, f ∘ g⟩

instance : functor P.apply := {map := @map P}

theorem map_eq {α β : Type*} (f : α → β) (a : P.A) (g : P.B a → α) :
  @functor.map P.apply _ _ _ f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
rfl

theorem id_map {α : Type*} : ∀ x : P.apply α, id <$> x = id x :=
λ ⟨a, b⟩, rfl

theorem comp_map {α β γ : Type*} (f : α → β) (g : β → γ) :
  ∀ x : P.apply α, (g ∘ f) <$> x = g <$> (f <$> x) :=
λ ⟨a, b⟩, rfl

instance : is_lawful_functor P.apply :=
{id_map := @id_map P, comp_map := @comp_map P}

inductive W
| mk (a : P.A) (f : P.B a → W) : W

def W_dest : W P → P.apply (W P)
| ⟨a, f⟩ := ⟨a, f⟩

def W_mk : P.apply (W P) → W P
| ⟨a, f⟩ := ⟨a, f⟩

@[simp] theorem W_dest_W_mk (p : P.apply (W P)) : P.W_dest (P.W_mk p) = p :=
by cases p; reflexivity

@[simp] theorem W_mk_W_dest (p : W P) : P.W_mk (P.W_dest p) = p :=
by cases p; reflexivity

end pfunctor

/-
Quotients of polynomial functors.

Roughly speaking, saying that `F` is a quotient of a polynomial functor means that for each `α`,
elements of `F α` are represented by pairs `⟨a, f⟩`, where `a` is the shape of the object and
`f` indexes the relevant elements of `α`, in a suitably natural manner.
-/

class qpf (F : Type u → Type u) [functor F] :=
(P         : pfunctor.{u})
(abs       : Π {α}, P.apply α → F α)
(repr      : Π {α}, F α → P.apply α)
(abs_repr  : ∀ {α} (x : F α), abs (repr x) = x)
(abs_map   : ∀ {α β} (f : α → β) (p : P.apply α), abs (f <$> p) = f <$> abs p)

namespace qpf
variables {F : Type u → Type u} [functor F] [q : qpf F]
include q

attribute [simp] abs_repr

/-
Show that every qpf is a lawful functor.

Note: every functor has a field, map_comp, and is_lawful_functor has the defining
characterization. We can only propagate the assumption.
-/

theorem id_map {α : Type*} (x : F α) : id <$> x = x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map], reflexivity }

theorem comp_map {α β γ : Type*} (f : α → β) (g : β → γ) (x : F α) :
  (g ∘ f) <$> x = g <$> f <$> x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map, ←abs_map, ←abs_map], reflexivity }

theorem is_lawful_functor
  (h : ∀ α β : Type u, @functor.map_const F _ α _ = functor.map ∘ function.const β) : is_lawful_functor F :=
{ map_const_eq := h,
  id_map := @id_map F _ _,
  comp_map := @comp_map F _ _ }

/-
Think of trees in the `W` type corresponding to `P` as representatives of elements of the
least fixed point of `F`, and assign a canonical representative to each equivalence class
of trees.
-/

/-- does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
def recF {α : Type*} (g : F α → α) : q.P.W → α
| ⟨a, f⟩ := g (abs ⟨a, λ x, recF (f x)⟩)

theorem recF_eq {α : Type*} (g : F α → α) (x : q.P.W) :
  recF g x = g (abs (recF g <$> q.P.W_dest x)) :=
by cases x; reflexivity

theorem recF_eq' {α : Type*} (g : F α → α) (a : q.P.A) (f : q.P.B a → q.P.W) :
  recF g ⟨a, f⟩ = g (abs (recF g <$> ⟨a, f⟩)) :=
rfl

/-- two trees are equivalent if their F-abstractions are -/
inductive Wequiv : q.P.W → q.P.W → Prop
| ind (a : q.P.A) (f f' : q.P.B a → q.P.W) :
    (∀ x, Wequiv (f x) (f' x)) → Wequiv ⟨a, f⟩ ⟨a, f'⟩
| abs (a : q.P.A) (f : q.P.B a → q.P.W) (a' : q.P.A) (f' : q.P.B a' → q.P.W) :
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → Wequiv ⟨a, f⟩ ⟨a', f'⟩
| trans (u v w : q.P.W) : Wequiv u v → Wequiv v w → Wequiv u w

/-- recF is insensitive to the representation -/
theorem recF_eq_of_Wequiv {α : Type u} (u : F α → α) (x y : q.P.W) :
  Wequiv x y → recF u x = recF u y :=
begin
  cases x with a f, cases y with b g,
  intro h, induction h,
  case qpf.Wequiv.ind : a f f' h ih
    { simp only [recF_eq', pfunctor.map_eq, function.comp, ih] },
  case qpf.Wequiv.abs : a f a' f' h ih
    { simp only [recF_eq', abs_map, h] },
  case qpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { exact eq.trans ih₁ ih₂ }
end

theorem Wequiv.abs' (x y : q.P.W) (h : abs (q.P.W_dest x) = abs (q.P.W_dest y)) :
  Wequiv x y :=
by { cases x, cases y, apply Wequiv.abs, apply h }

theorem Wequiv.refl (x : q.P.W) : Wequiv x x :=
by cases x with a f; exact Wequiv.abs a f a f rfl

theorem Wequiv.symm (x y : q.P.W) : Wequiv x y → Wequiv y x :=
begin
  cases x with a f, cases y with b g,
  intro h, induction h,
  case qpf.Wequiv.ind : a f f' h ih
    { exact Wequiv.ind _ _ _ ih },
  case qpf.Wequiv.abs : a f a' f' h ih
    { exact Wequiv.abs _ _ _ _ h.symm },
  case qpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { exact qpf.Wequiv.trans _ _ _ ih₂ ih₁}
end

/-- maps every element of the W type to a canonical representative -/
def Wrepr : q.P.W → q.P.W := recF (q.P.W_mk ∘ repr)

theorem Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x :=
begin
  induction x with a f ih,
  apply Wequiv.trans,
  { change Wequiv (Wrepr ⟨a, f⟩) (q.P.W_mk (Wrepr <$> ⟨a, f⟩)),
    apply Wequiv.abs',
    have : Wrepr ⟨a, f⟩ = q.P.W_mk (repr (abs (Wrepr <$> ⟨a, f⟩))) := rfl,
    rw [this, pfunctor.W_dest_W_mk, abs_repr],
    reflexivity },
  apply Wequiv.ind, exact ih
end

/-
Define the fixed point as the quotient of trees under the equivalence relation.
-/

def W_setoid : setoid q.P.W :=
⟨Wequiv, @Wequiv.refl _ _ _, @Wequiv.symm _ _ _, @Wequiv.trans _ _ _⟩

local attribute [instance] W_setoid

def fix (F : Type u → Type u) [functor F] [q : qpf F]:= quotient (W_setoid : setoid q.P.W)

def fix.rec {α : Type*} (g : F α → α) : fix F → α :=
quot.lift (recF g) (recF_eq_of_Wequiv g)

def fix_to_W : fix F → q.P.W :=
quotient.lift Wrepr (recF_eq_of_Wequiv (λ x, q.P.W_mk (repr x)))

def fix.mk (x : F (fix F)) : fix F := quot.mk _ (q.P.W_mk (fix_to_W <$> repr x))

def fix.dest : fix F → F (fix F) := fix.rec (functor.map fix.mk)

theorem fix.rec_eq {α : Type*} (g : F α → α) (x : F (fix F)) :
  fix.rec g (fix.mk x) = g (fix.rec g <$> x) :=
have recF g ∘ fix_to_W = fix.rec g,
  by { apply funext, apply quotient.ind, intro x, apply recF_eq_of_Wequiv,
       apply Wrepr_equiv },
begin
  conv { to_lhs, rw [fix.rec, fix.mk], dsimp },
  cases h : repr x with a f,
  rw [pfunctor.map_eq, recF_eq, ←pfunctor.map_eq, pfunctor.W_dest_W_mk, ←pfunctor.comp_map,
      abs_map, ←h, abs_repr, this]
end

theorem fix.ind_aux (a : q.P.A) (f : q.P.B a → q.P.W) :
  fix.mk (abs ⟨a, λ x, ⟦f x⟧⟩) = ⟦⟨a, f⟩⟧ :=
have fix.mk (abs ⟨a, λ x, ⟦f x⟧⟩) = ⟦Wrepr ⟨a, f⟩⟧,
  begin
    apply quot.sound, apply Wequiv.abs',
    rw [pfunctor.W_dest_W_mk, abs_map, abs_repr, ←abs_map, pfunctor.map_eq],
    conv { to_rhs, simp only [Wrepr, recF_eq, pfunctor.W_dest_W_mk, abs_repr] },
    reflexivity
  end,
by { rw this, apply quot.sound, apply Wrepr_equiv }

theorem fix.ind {α : Type*} (g₁ g₂ : fix F → α)
    (h : ∀ x : F (fix F), g₁ <$> x = g₂ <$> x → g₁ (fix.mk x) = g₂ (fix.mk x)) :
  ∀ x, g₁ x = g₂ x :=
begin
  apply quot.ind,
  intro x,
  induction x with a f ih,
  change g₁ ⟦⟨a, f⟩⟧ = g₂ ⟦⟨a, f⟩⟧,
  rw [←fix.ind_aux a f], apply h,
  rw [←abs_map, ←abs_map, pfunctor.map_eq, pfunctor.map_eq],
  dsimp [function.comp],
  congr, ext x, apply ih
end

theorem fix.rec_unique {α : Type*} (g : F α → α) (h : fix F → α)
    (hyp : ∀ x, h (fix.mk x) = g (h <$> x)) :
  fix.rec g = h :=
begin
  ext x,
  apply fix.ind,
  intros x hyp',
  rw [hyp, ←hyp', fix.rec_eq]
end

theorem fix.mk_dest (x : fix F) : fix.mk (fix.dest x) = x :=
begin
  change (fix.mk ∘ fix.dest) x = id x,
  apply fix.ind,
  intro x, dsimp,
  rw [fix.dest, fix.rec_eq, id_map, comp_map],
  intro h, rw h
end

theorem fix.dest_mk (x : F (fix F)) : fix.dest (fix.mk x) = x :=
begin
  unfold fix.dest, rw [fix.rec_eq, ←fix.dest, ←comp_map],
  conv { to_rhs, rw ←(id_map x) },
  congr, ext x, apply fix.mk_dest
end

end qpf

/- Axiomatize the M construction for now -/

-- TODO: needed only because we axiomatize M
noncomputable theory

namespace pfunctor

axiom M (P : pfunctor.{u}) : Type u

-- TODO: are the universe ascriptions correct?
variables {P : pfunctor.{u}} {α : Type u}

axiom M_dest : M P → P.apply (M P)

axiom M_corec : (α → P.apply α) → (α → M P)

axiom M_dest_corec (g : α → P.apply α) (x : α) :
  M_dest (M_corec g x) = M_corec g <$> g x

axiom M_bisim {α : Type*} (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      M_dest x = ⟨a, f⟩ ∧
      M_dest y = ⟨a, f'⟩ ∧
      ∀ i, R (f i) (f' i)) :
  ∀ x y, R x y → x = y

theorem M_bisim' {α : Type*} (Q : α → Prop) (u v : α → M P)
    (h : ∀ x, Q x → ∃ a f f',
      M_dest (u x) = ⟨a, f⟩ ∧
      M_dest (v x) = ⟨a, f'⟩ ∧
      ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
  ∀ x, Q x → u x = v x :=
λ x Qx,
let R := λ w z : M P, ∃ x', Q x' ∧ w = u x' ∧ z = v x' in
@M_bisim P (M P) R
  (λ x y ⟨x', Qx', xeq, yeq⟩,
    let ⟨a, f, f', ux'eq, vx'eq, h'⟩ := h x' Qx' in
      ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
  _ _ ⟨x, Qx, rfl, rfl⟩

-- for the record, show M_bisim follows from M_bisim'
theorem M_bisim_equiv (R : M P → M P → Prop)
    (h : ∀ x y, R x y → ∃ a f f',
      M_dest x = ⟨a, f⟩ ∧
      M_dest y = ⟨a, f'⟩ ∧
      ∀ i, R (f i) (f' i)) :
  ∀ x y, R x y → x = y :=
λ x y Rxy,
let Q : M P × M P → Prop := λ p, R p.fst p.snd in
M_bisim' Q prod.fst prod.snd
  (λ p Qp,
    let ⟨a, f, f', hx, hy, h'⟩ := h p.fst p.snd Qp in
    ⟨a, f, f', hx, hy, λ i, ⟨⟨f i, f' i⟩, h' i, rfl, rfl⟩⟩)
  ⟨x, y⟩ Rxy

theorem M_corec_unique (g : α → P.apply α) (f : α → M P)
    (hyp : ∀ x, M_dest (f x) = f <$> (g x)) :
  f = M_corec g :=
begin
  ext x,
  apply M_bisim' (λ x, true) _ _ _ _ trivial,
  clear x,
  intros x _,
  cases gxeq : g x with a f',
  have h₀ : M_dest (f x) = ⟨a, f ∘ f'⟩,
  { rw [hyp, gxeq, pfunctor.map_eq] },
  have h₁ : M_dest (M_corec g x) = ⟨a, M_corec g ∘ f'⟩,
  { rw [M_dest_corec, gxeq, pfunctor.map_eq], },
  refine ⟨_, _, _, h₀, h₁, _⟩,
  intro i,
  exact ⟨f' i, trivial, rfl, rfl⟩
end

def M_mk : P.apply (M P) → M P := M_corec (λ x, M_dest <$> x)

theorem M_mk_M_dest (x : M P) : M_mk (M_dest x) = x :=
begin
  apply M_bisim' (λ x, true) (M_mk ∘ M_dest) _ _ _ trivial,
  clear x,
  intros x _,
  cases Mxeq : M_dest x with a f',
  have : M_dest (M_mk (M_dest x)) = ⟨a, _⟩,
  { rw [M_mk, M_dest_corec, Mxeq, pfunctor.map_eq, pfunctor.map_eq] },
  refine ⟨_, _, _, this, rfl, _⟩,
  intro i,
  exact ⟨f' i, trivial, rfl, rfl⟩
end

theorem M_dest_M_mk (x : P.apply (M P)) : M_dest (M_mk x) = x :=
begin
  have : M_mk ∘ M_dest = id := funext M_mk_M_dest,
  rw [M_mk, M_dest_corec, ←comp_map, ←M_mk, this, id_map, id]
end

end pfunctor

/-
Construct the final coalebra to a qpf.
-/

namespace qpf
variables {F : Type u → Type u} [functor F] [q : qpf F]
include q

/-- does recursion on `q.P.M` using `g : α → F α` rather than `g : α → P α` -/
def corecF {α : Type*} (g : α → F α) : α → q.P.M :=
pfunctor.M_corec (λ x, repr (g x))

theorem corecF_eq {α : Type*} (g : α → F α) (x : α) :
  pfunctor.M_dest (corecF g x) = corecF g <$> repr (g x) :=
by rw [corecF, pfunctor.M_dest_corec]

/- Equivalence -/

/- A pre-congruence on q.P.M *viewed as an F-coalgebra*. Not necessarily symmetric. -/
def is_precongr (r : q.P.M → q.P.M → Prop) : Prop :=
  ∀ ⦃x y⦄, r x y →
    abs (quot.mk r <$> pfunctor.M_dest x) = abs (quot.mk r <$> pfunctor.M_dest y)

/- The maximal congruence on q.P.M -/
def Mcongr : q.P.M → q.P.M → Prop :=
λ x y, ∃ r, is_precongr r ∧ r x y

def cofix (F : Type u → Type u) [functor F] [q : qpf F]:= quot (@Mcongr F _ q)

def cofix.corec {α : Type*} (g : α → F α) : α → cofix F :=
λ x, quot.mk  _ (corecF g x)

def cofix.dest : cofix F → F (cofix F) :=
quot.lift
  (λ x, quot.mk Mcongr <$> (abs (pfunctor.M_dest x)))
  begin
    rintros x y ⟨r, pr, rxy⟩, dsimp,
    have : ∀ x y, r x y → Mcongr x y,
    { intros x y h, exact ⟨r, pr, h⟩ },
    rw [←quot.factor_mk_eq _ _ this], dsimp,
    conv { to_lhs, rw [comp_map, ←abs_map, pr rxy, abs_map, ←comp_map] }
  end

theorem cofix.dest_corec {α : Type u} (g : α → F α) (x : α) :
  cofix.dest (cofix.corec g x) = cofix.corec g <$> g x :=
begin
  conv { to_lhs, rw [cofix.dest, cofix.corec] }, dsimp,
  rw [corecF_eq, abs_map, abs_repr, ←comp_map], reflexivity
end

private theorem cofix.bisim_aux
    (r : cofix F → cofix F → Prop)
    (h' : ∀ x, r x x)
    (h : ∀ x y, r x y → quot.mk r <$> cofix.dest x = quot.mk r <$> cofix.dest y) :
  ∀ x y, r x y → x = y :=
begin
  intro x, apply quot.induction_on x, clear x,
  intros x y, apply quot.induction_on y, clear y,
  intros y rxy,
  apply quot.sound,
  let r' := λ x y, r (quot.mk _ x) (quot.mk _ y),
  have : is_precongr r',
  { intros a b r'ab,
    have  h₀: quot.mk r <$> quot.mk Mcongr <$> abs (pfunctor.M_dest a) =
              quot.mk r <$> quot.mk Mcongr <$> abs (pfunctor.M_dest b) := h _ _ r'ab,
    have h₁ : ∀ u v : q.P.M, Mcongr u v → quot.mk r' u = quot.mk r' v,
    { intros u v cuv, apply quot.sound, dsimp [r'], rw quot.sound cuv, apply h' },
    let f : quot r → quot r' := quot.lift (quot.lift (quot.mk r') h₁)
      begin
        intro c, apply quot.induction_on c, clear c,
        intros c d, apply quot.induction_on d, clear d,
        intros d rcd, apply quot.sound, apply rcd
      end,
    have : f ∘ quot.mk r ∘ quot.mk Mcongr = quot.mk r' := rfl,
    rw [←this, pfunctor.comp_map _ _ f, pfunctor.comp_map _ _ (quot.mk r),
          abs_map, abs_map, abs_map, h₀],
    rw [pfunctor.comp_map _ _ f, pfunctor.comp_map _ _ (quot.mk r),
          abs_map, abs_map, abs_map] },
  refine ⟨r', this, rxy⟩
end

theorem cofix.bisim
    (r : cofix F → cofix F → Prop)
    (h : ∀ x y, r x y → quot.mk r <$> cofix.dest x = quot.mk r <$> cofix.dest y) :
  ∀ x y, r x y → x = y :=
let r' x y := x = y ∨ r x y in
begin
  intros x y rxy,
  apply cofix.bisim_aux r',
  { intro x, left, reflexivity },
  { intros x y r'xy,
    cases r'xy, { rw r'xy },
    have : ∀ x y, r x y → r' x y := λ x y h, or.inr h,
    rw ←quot.factor_mk_eq _ _ this, dsimp,
    rw [@comp_map _ _ q _ _ _ (quot.mk r), @comp_map _ _ q _ _ _ (quot.mk r)],
    rw h _ _ r'xy },
  right, exact rxy
end

/-
TODO:
- define other two versions of relation lifting (via subtypes, via P)
- derive other bisimulation principles.
- define mk and prove identities.
-/

end qpf

/-
Composition of qpfs.
-/

namespace pfunctor

/-
def comp : pfunctor.{u} → pfunctor.{u} → pfunctor.{u}
| ⟨A₂, B₂⟩ ⟨A₁, B₁⟩ := ⟨Σ a₂ : A₂, B₂ a₂ → A₁, λ ⟨a₂, a₁⟩, Σ u : B₂ a₂, B₁ (a₁ u)⟩
-/

def comp (P₂ P₁ : pfunctor.{u}) : pfunctor.{u} :=
⟨ Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1,
  λ a₂a₁, Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u) ⟩

end pfunctor

namespace qpf

variables {F₂ : Type u → Type u} [functor F₂] [q₂ : qpf F₂]
variables {F₁ : Type u → Type u} [functor F₁] [q₁ : qpf F₁]
include q₂ q₁

def comp : qpf (functor.comp F₂ F₁) :=
{ P := pfunctor.comp (q₂.P) (q₁.P),
  abs := λ α,
    begin
      dsimp [functor.comp],
      intro p,
      exact abs ⟨p.1.1, λ x, abs ⟨p.1.2 x, λ y, p.2 ⟨x, y⟩⟩⟩
    end,
  repr := λ α,
    begin
      dsimp [functor.comp],
      intro y,
      refine ⟨⟨(repr y).1, λ u, (repr ((repr y).2 u)).1⟩, _⟩,
      dsimp [pfunctor.comp],
      intro x,
      exact (repr ((repr y).2 x.1)).snd x.2
    end,
  abs_repr := λ α,
    begin
      abstract {
      dsimp [functor.comp],
      intro x,
      conv { to_rhs, rw ←abs_repr x},
      cases h : repr x with a f,
      dsimp,
      congr,
      ext x,
      cases h' : repr (f x) with b g,
      dsimp, rw [←h', abs_repr] }
    end,
  abs_map := λ α β f,
    begin
      abstract {
      dsimp [functor.comp, pfunctor.comp],
      intro p,
      cases p with a g, dsimp,
      cases a with b h, dsimp,
      symmetry,
      transitivity,
      symmetry,
      apply abs_map,
      congr,
      rw pfunctor.map_eq,
      dsimp [function.comp],
      simp [abs_map],
      split,
      reflexivity,
      ext x,
      rw ←abs_map,
      reflexivity }
    end
}

end qpf


/-
Quotients.

We show that if `F` is a qpf and `G` is a suitable quotient of `F`, then `G` is a qpf.
-/

namespace qpf
variables {F : Type u → Type u} [functor F] [q : qpf F]
variables {G : Type u → Type u} [functor G]
variable  {FG_abs  : Π {α}, F α → G α}
variable  {FG_repr : Π {α}, G α → F α}

def quotient_qpf
    (FG_abs_repr : Π {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map  : ∀ {α β} (f : α → β) (x : F α), FG_abs (f <$> x) = f <$> FG_abs x) :
  qpf G :=
{ P        := q.P,
  abs      := λ {α} p, FG_abs (abs p),
  repr     := λ {α} x, repr (FG_repr x),
  abs_repr := λ {α} x, by rw [abs_repr, FG_abs_repr],
  abs_map  := λ {α β} f x, by { rw [abs_map, FG_abs_map] } }

end qpf

#exit
import group_theory.subgroup group_theory.perm

universe u

open finset equiv equiv.perm

class simple_group {G : Type*} [group G] :=
(simple : ∀ (H : set G) [normal_subgroup H], H = set.univ ∨ H = is_subgroup.trivial G)

variables {G : Type*} [group G] [fintype G] [decidable_eq G]

def conjugacy_class (a : G) : finset G :=
(@univ G _).image (λ x, x * a * x⁻¹)

@[simp] lemma mem_conjugacy_class {a b : G} : b ∈ conjugacy_class a ↔ is_conj a b :=
by simp [conjugacy_class, mem_image, is_conj, eq_comm]

def subgroup_closure (s : finset G) : finset G :=
insert 1 ((s.product s).image (λ a, a.1 * a.2⁻¹))

instance subgroup_closure.is_subgroup (s : finset G) :
  is_subgroup (↑(subgroup_closure s) : set G) :=
{ one_mem := by simp [subgroup_closure],
  mul_mem := sorry,
  inv_mem := sorry }

def alternating (α : Type u) [fintype α] [decidable_eq α] : Type u :=
is_group_hom.ker (sign : perm α → units ℤ)

instance (α : Type u) [fintype α] [decidable_eq α] : group (alternating α) :=
by unfold alternating; apply_instance

instance (α : Type u) [fintype α] [decidable_eq α] :
  fintype (alternating α) :=
by simp [alternating, is_group_hom.ker];
exact subtype.fintype _

#eval conjugacy_class (show alternating (fin 5),
  from ⟨swap 1 2 * swap 2 3, by simp [is_group_hom.ker]; refl⟩)



#exit
def next_aux (N : nat) : list nat -> nat
| [] := 0
| (hd :: tl) := if hd < N then 0 else next_aux tl + 1

def next (m : nat) : list nat -> list nat
| [] := []
| (0 :: tl) := tl
| ((n+1) :: tl) := let index := next_aux (n+1) tl,
    B := n :: list.take index tl,
    G := list.drop index tl in
    ((++ B)^[m+1] B) ++ G

-- Beklemishev's worms
def worm_step (initial : nat) : Π step : nat, list nat
| 0 := [initial]
| (m+1) := next m (worm_step m)

#eval (list.range 10).map (worm_step 3)

-- It will terminate
theorem worm_principle : ∀ n, ∃ s, worm_step n s = []
| 0 := ⟨1, rfl⟩
| (n+1) := begin


end


-- def Fin : nat → Type
--   | 0 := empty
--   | (n+1) := option (Fin n)

inductive Fin : nat → Type
| mk {n : ℕ} : option (Fin n) → Fin (n + 1)


#exit

import analysis.topology.continuity

#print axioms continuous

local attribute [instance] classical.prop_decidable

import analysis.topology.continuity

lemma continuous_of_const {α : Type*} {β : Type*} [topological_space α]
  [topological_space β] {f : α → β} (h : ∀a b, f a = f b) : continuous f :=
λ s hs, _

#exit
example {α : Type*} (r : α → α → Prop)
  (h : ∀ f : ℕ → α, ∃ n, ¬r (f (n + 1)) (f n)) :
  well_founded r :=
let f : Π a : α, �� acc r a → {b : α // ¬ acc r b ∧ r b a} :=
  λ a ha, classical.indefinite_description _
    (classical.by_contradiction
      (λ hc, ha $ acc.intro _ (λ y hy,
        classical.by_contradiction (λ hy1, hc ⟨y, hy1, hy⟩)))) in
well_founded.intro
  (λ a, classical.by_contradiction
    (λ ha, let g : Π n : ℕ, {b : α // ¬ acc r b} := λ n, nat.rec_on n ⟨a, ha⟩
        (λ n b, ⟨f b.1 b.2, (f b.1 b.2).2.1⟩ ) in
      have hg : ∀ n, r (g (n + 1)) (g n),
        from λ n, nat.rec_on n (f _ _).2.2
          (λ n hn, (f _ _).2.2),
      exists.elim (h (subtype.val ∘ g)) (λ n hn, hn (hg _))))



example {α : Type*} (r : α → α → Prop)
  (h : well_founded r) (f : ℕ → α) :
  ∃ n, ¬r (f (n + 1)) (f n) :=
classical.by_contradiction (λ hr,
  @well_founded.fix α (λ a, ∀ n, a ≠ f n) r h
  (λ a ih n hn, ih (f (n + 1)) (classical.by_contradiction (hn.symm ▸ λ h, hr ⟨_, h⟩)) (n + 1) rfl)
  (f 0) 0 rfl )

lemma well_founded_iff_descending_chain {α : Type*} (r : α → α → Prop) :
  well_founded r ↔ ∀ f : ℕ → α, ∃ n, ¬ r (f (n + 1)) (f n) :=
⟨λ h f, classical.by_contradiction (λ hr,
    @well_founded.fix α (λ a, ∀ n, a ≠ f n) r h
      (λ a ih n hn, ih (f (n + 1))
        (classical.by_contradiction (hn.symm ▸ λ h, hr ⟨_, h⟩)) (n + 1) rfl)
      (f 0) 0 rfl),
  λ h, let f : Π a : α, ¬ acc r a → {b : α // ¬ acc r b ∧ r b a} :=
      λ a ha, classical.indefinite_description _
        (classical.by_contradiction
          (λ hc, ha $ acc.intro _ (λ y hy,
            classical.by_contradiction (λ hy1, hc ⟨y, hy1, hy⟩)))) in
    well_founded.intro
      (λ a, classical.by_contradiction
        (λ ha,
          let g : Π n : ℕ, {b : α // ¬ acc r b} :=
            λ n, nat.rec_on n ⟨a, ha⟩
              (λ n b, ���f b.1 b.2, (f b.1 b.2).2.1⟩) in
          have hg : ∀ n, r (g (n + 1)) (g n),
            from λ n, nat.rec_on n (f _ _).2.2
              (λ n hn, (f _ _).2.2),
          exists.elim (h (subtype.val ∘ g)) (λ n hn, hn (hg _))))⟩

#exit
import data.set.lattice order.order_iso data.quot

universes u v

noncomputable theory

axiom choice2_aux {α : Sort u} : { choice : α → α // ∀ (a b : α), choice a = choice b }

def choice2 : Π {α : Sort u}, α → α := λ _, choice2_aux.1

lemma choice2_spec : ∀ {α : Sort u} (a b : α), choice2 a = choice2 b := λ _, choice2_aux.2

axiom univalence : ∀ {α β : Sort u}, α ≃ β → α = β

lemma trunc.out2 {α : Sort u} (a : trunc α) : α := trunc.lift_on a choice2 choice2_spec

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

end diaconescu

def old_choice {α : Sort u} : nonempty α → α :=
psum.rec_on (em α) (λ a _, a)
  (function.swap (((∘) ∘ (∘)) false.elim nonempty.elim))
#print axioms old_choice
open tactic declaration

#eval do d ← get_decl `old_choice,
  match d with
  | defn _ _ _ v _ _ := do e ← tactic.whnf v
      tactic.transparency.all tt, trace e, skip
  | _ := skip
  end

#exit
open set
section chain
parameters {α : Type u} (r : α → α → Prop)
local infix ` ≺ `:50  := r

/-- A chain is a subset `c` satisfying
  `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ c`. -/
def chain (c : set α) := pairwise_on c (λx y, x ≺ y ∨ y ≺ x)
parameters {r}

theorem chain.total_of_refl [is_refl α r]
  {c} (H : chain c) {x y} (hx : x ∈ c) (hy : y ∈ c) :
  x ≺ y ∨ y ≺ x :=
if e : x = y then or.inl (e ▸ refl _) else H _ hx _ hy e

theorem chain.directed [is_refl α r]
  {c} (H : chain c) {x y} (hx : x ∈ c) (hy : y ∈ c) :
  ∃ z, z ∈ c ∧ x ≺ z ∧ y ≺ z :=
match H.total_of_refl hx hy with
| or.inl h := ⟨y, hy, h, refl _⟩
| or.inr h := ⟨x, hx, refl _, h⟩
end

theorem chain.mono {c c'} : c' ⊆ c → chain c → chain c' :=
pairwise_on.mono

theorem chain.directed_on [is_refl α r] {c} (H : chain c) : directed_on (≺) c :=
λ x xc y yc, let ⟨z, hz, h⟩ := H.directed xc yc in ⟨z, hz, h⟩

theorem chain_insert {c : set α} {a : α} (hc : chain c) (ha : ∀b∈c, b ≠ a → a ≺ b ∨ b ≺ a) :
  chain (insert a c) :=
forall_insert_of_forall
  (assume x hx, forall_insert_of_forall (hc x hx) (assume hneq, (ha x hx hneq).symm))
  (forall_insert_of_forall (assume x hx hneq, ha x hx $ assume h', hneq h'.symm) (assume h, (h rfl).rec _))

def super_chain (c₁ c₂ : set α) := chain c₂ ∧ c₁ ⊂ c₂

def is_max_chain (c : set α) := chain c ∧ ¬ (∃c', super_chain c c')

def succ_chain (c : set α) : set α :=
psum.rec_on (em2 {c' : set α // chain c ∧ super_chain c c'}) subtype.val (λ _, c)

theorem succ_spec {c : set α} (h : {c' // chain c ∧ super_chain c c'}) :
  super_chain c (succ_chain c) :=
let ⟨c', hc'⟩ := h in
have chain c ∧ super_chain c (some h),
  from @some_spec _ (λc', chain c ∧ super_chain c c') _,
by simp [succ_chain, dif_pos, h, this.right]

theorem chain_succ {c : set α} (hc : chain c) : chain (succ_chain c) :=
if h : ∃c', chain c ∧ super_chain c c' then
  (succ_spec h).left
else
  by simp [succ_chain, dif_neg, h]; exact hc

theorem super_of_not_max {c : set α} (hc₁ : chain c) (hc₂ : ¬ is_max_chain c) :
  super_chain c (succ_chain c) :=
begin
  simp [is_max_chain, not_and_distrib, not_forall_not] at hc₂,
  cases hc₂.neg_resolve_left hc₁ with c' hc',
  exact succ_spec ⟨c', hc₁, hc'⟩
end

theorem succ_increasing {c : set α} : c ⊆ succ_chain c :=
if h : ∃c', chain c ∧ super_chain c c' then
  have super_chain c (succ_chain c), from succ_spec h,
  this.right.left
else by simp [succ_chain, dif_neg, h, subset.refl]

inductive chain_closure : set α → Prop
| succ : ∀{s}, chain_closure s → chain_closure (succ_chain s)
| union : ∀{s}, (∀a∈s, chain_closure a) → chain_closure (⋃₀ s)

theorem chain_closure_empty : chain_closure ∅ :=
have chain_closure (⋃₀ ∅),
  from chain_closure.union $ assume a h, h.rec _,
by simp at this; assumption

theorem chain_closure_closure : chain_closure (⋃₀ chain_closure) :=
chain_closure.union $ assume s hs, hs

variables {c c₁ c₂ c₃ : set α}

private lemma chain_closure_succ_total_aux (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂)
  (h : ∀{c₃}, chain_closure c₃ → c₃ ⊆ c₂ → c₂ = c₃ ∨ succ_chain c₃ ⊆ c₂) :
  c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁ :=
begin
  induction hc₁,
  case _root_.zorn.chain_closure.succ : c₃ hc₃ ih {
    cases ih with ih ih,
    { have h := h hc₃ ih,
      cases h with h h,
      { exact or.inr (h ▸ subset.refl _) },
      { exact or.inl h } },
    { exact or.inr (subset.trans ih succ_increasing) } },
  case _root_.zorn.chain_closure.union : s hs ih {
    refine (classical.or_iff_not_imp_right.2 $ λ hn, sUnion_subset $ λ a ha, _),
    apply (ih a ha).resolve_right,
    apply mt (λ h, _) hn,
    exact subset.trans h (subset_sUnion_of_mem ha) }
end

private lemma chain_closure_succ_total (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂) (h : c₁ ⊆ c₂) :
  c₂ = c₁ ∨ succ_chain c₁ ⊆ c₂ :=
begin
  induction hc₂ generalizing c₁ hc₁ h,
  case _root_.zorn.chain_closure.succ : c₂ hc₂ ih {
    have h₁ : c₁ ⊆ c₂ ∨ @succ_chain α r c₂ ⊆ c₁ :=
      (chain_closure_succ_total_aux hc₁ hc₂ $ assume c₁, ih),
    cases h₁ with h₁ h₁,
    { have h₂ := ih hc₁ h₁,
      cases h₂ with h₂ h₂,
      { exact (or.inr $ h₂ ▸ subset.refl _) },
      { exact (or.inr $ subset.trans h₂ succ_increasing) } },
    { exact (or.inl $ subset.antisymm h₁ h) } },
  case _root_.zorn.chain_closure.union : s hs ih {
    apply or.imp_left (assume h', subset.antisymm h' h),
    apply classical.by_contradiction,
    simp [not_or_distrib, sUnion_subset_iff, classical.not_forall],
    intros c₃ hc₃ h₁ h₂,
    have h := chain_closure_succ_total_aux hc₁ (hs c₃ hc₃) (assume c₄, ih _ hc₃),
    cases h with h h,
    { have h' := ih c₃ hc₃ hc₁ h,
      cases h' with h' h',
      { exact (h₁ $ h' ▸ subset.refl _) },
      { exact (h₂ $ subset.trans h' $ subset_sUnion_of_mem hc₃) } },
    { exact (h₁ $ subset.trans succ_increasing h) } }
end

theorem chain_closure_total (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂) : c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
have c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁,
  from chain_closure_succ_total_aux hc₁ hc₂ $ assume c₃ hc₃, chain_closure_succ_total hc₃ hc₂,
or.imp_right (assume : succ_chain c₂ ⊆ c₁, subset.trans succ_increasing this) this

theorem chain_closure_succ_fixpoint (hc₁ : chain_closure c₁) (hc₂ : chain_closure c₂)
  (h_eq : succ_chain c₂ = c₂) : c₁ ⊆ c₂ :=
begin
  induction hc₁,
  case _root_.zorn.chain_closure.succ : c₁ hc₁ h {
    exact or.elim (chain_closure_succ_total hc₁ hc₂ h)
      (assume h, h ▸ h_eq.symm ▸ subset.refl c₂) id },
  case _root_.zorn.chain_closure.union : s hs ih {
    exact (sUnion_subset $ assume c₁ hc₁, ih c₁ hc₁) }
end

theorem chain_closure_succ_fixpoint_iff (hc : chain_closure c) :
  succ_chain c = c ↔ c = ⋃₀ chain_closure :=
⟨assume h, subset.antisymm
    (subset_sUnion_of_mem hc)
    (chain_closure_succ_fixpoint chain_closure_closure hc h),
  assume : c = ⋃₀{c : set α | chain_closure c},
  subset.antisymm
    (calc succ_chain c ⊆ ⋃₀{c : set α | chain_closure c} :
        subset_sUnion_of_mem $ chain_closure.succ hc
      ... = c : this.symm)
    succ_increasing⟩

theorem chain_chain_closure (hc : chain_closure c) : chain c :=
begin
  induction hc,
  case _root_.zorn.chain_closure.succ : c hc h {
    exact chain_succ h },
  case _root_.zorn.chain_closure.union : s hs h {
    have h : ∀c∈s, zorn.chain c := h,
    exact assume c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq,
      have t₁ ⊆ t₂ ∨ t₂ ⊆ t₁, from chain_closure_total (hs _ ht₁) (hs _ ht₂),
      or.elim this
        (assume : t₁ ⊆ t₂, h t₂ ht₂ c₁ (this hc₁) c₂ hc₂ hneq)
        (assume : t₂ ⊆ t₁, h t₁ ht₁ c₁ hc₁ c₂ (this hc₂) hneq) }
end

def max_chain := ⋃₀ chain_closure

/-- Hausdorff's maximality principle

There exists a maximal totally ordered subset of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
theorem max_chain_spec : is_max_chain max_chain :=
classical.by_contradiction $
assume : ¬ is_max_chain (⋃₀ chain_closure),
have super_chain (⋃₀ chain_closure) (succ_chain (⋃₀ chain_closure)),
  from super_of_not_max (chain_chain_closure chain_closure_closure) this,
let ⟨h₁, h₂, (h₃ : (⋃₀ chain_closure) ≠ succ_chain (⋃₀ chain_closure))⟩ := this in
have succ_chain (⋃₀ chain_closure) = (⋃₀ chain_closure),
  from (chain_closure_succ_fixpoint_iff chain_closure_closure).mpr rfl,
h₃ this.symm

/-- Zorn's lemma

If every chain has an upper bound, then there is a maximal element -/
theorem zorn (h : ∀c, chain c → ∃ub, ∀a∈c, a ≺ ub) (trans : ∀{a b c}, a ≺ b → b ≺ c → a ≺ c) :
  ∃m, ∀a, m ≺ a → a ≺ m :=
have ∃ub, ∀a∈max_chain, a ≺ ub,
  from h _ $ max_chain_spec.left,
let ⟨ub, (hub : ∀a∈max_chain, a ≺ ub)⟩ := this in
⟨ub, assume a ha,
  have chain (insert a max_chain),
    from chain_insert max_chain_spec.left $ assume b hb _, or.inr $ trans (hub b hb) ha,
  have a ∈ max_chain, from
    classical.by_contradiction $ assume h : a ∉ max_chain,
    max_chain_spec.right $ ⟨insert a max_chain, this, ssubset_insert h⟩,
  hub a this⟩
end

#exit
import analysis.exponential group_theory.quotient_group

axiom R_iso_C : {f : ℝ ≃ ℂ // is_add_group_hom f}

open quotient_group

def R_mod_Z_iso_units_C : quotient_add_group.quotient (gmultiples (1 : ℝ))
  ≃ units ℂ :=
calc units ℂ ≃

#exit
import data.real.basic tactic.norm_num
#print expr
--set_option pp.all true
lemma crazy (k l : ℕ) (h : l ≤ k): ((2:real)⁻¹)^k ≤ (2⁻¹)^l :=
begin
  apply pow_le_pow_of_le_one _ _ h,
  norm_num,
  norm_num1, norm_num1, simp,
  show (2 : ℝ)⁻¹ ≤ 1,
  norm_num1,

end

example {α : Type*} (h : α ≃ unit → false) {x : α} : α

import tactic.norm_num

set_option profiler true

lemma facebook_puzzle :
  let a := 154476802108746166441951315019919837485664325669565431700026634898253202035277999 in
  let b := 36875131794129999827197811565225474825492979968971970996283137471637224634055579 in
  let c := 4373612677928697257861252602371390152816537558161613618621437993378423467772036 in
  (a : ℚ) / (b + c) + b / (a + c) + c / (a + b) = 4 := by norm_num

#print facebook_puzzle
#print axioms facebook_puzzle

#exit
import data.complex.basic

lemma

import data.quot

section

variables {α : Sort*} {β : α → Sort*} {γ : Sort*} [s : ∀ a : α, setoid (β a)]
include s

instance pi.setoid : setoid (Π a : α, β a) :=
{ r := λ x y, ∀ a : α, x a ≈ y a,
  iseqv := ⟨λ x a, setoid.refl _,
    λ x y h a, setoid.symm (h a),
    λ x y z hxy hyz a, setoid.trans (hxy a) (hyz a)⟩ }

meta def setoid_to_setoid (x : Π a : α, quotient (s a)) :
  quotient (@pi.setoid α β _) :=
quotient.mk (λ a, quot.unquot (x a))

axiom quotient.lift_onₙ (x : Π a : α, quotient (s a))
  (f : (Π a : α, β a) → γ) (h : ∀ x₁ x₂ : Π a, β a,
  (∀ a, x₁ a ≈ x₂ a) → f x₁ = f x₂) : γ
end

#print classical.axiom_of_choice

lemma choice {α : Sort*} {β : α → Sort*} {r : Π (x : α), β x → Prop}
  (h : ∀ (x : α), ∃ (y : β x), r x y) :
    ∃ (f : Π (x : α), β x), ∀ (x : α), r x (f x) :=
begin

end
lemma quotient.lift_on

#exit
import tactic.ring data.complex.basic

lemma h (x : ℝ) : x / 3 + x / -2 = x / 6 := by ring
set_option pp.all true
#print h

example (x : ℂ) : x / 3 + x / 2 = 5 * x / 6 := by ring

#exit
import tactic.interactive


-- private meta def collect_proofs_in :
--   expr → list expr → list name × list expr → tactic (list name × list expr)
-- | e ctx (ns, hs) :=
-- let go (tac : list name × list expr → tactic (list name × list expr)) :
--   tactic (list name × list expr) :=
-- (do t ← infer_type e,
--    mcond (is_prop t) (do
--      first (hs.map $ λ h, do
--        t' ← infer_type h,
--        is_def_eq t t',
--        g ← target,
--        change $ g.replace (λ a n, if a = e then some h else none),
--        return (ns, hs)) <|>
--      (let (n, ns) := (match ns with
--         | [] := (`_x, [])
--         | (n :: ns) := (n, ns)
--         end : name × list name) in
--       do generalize e n,
--          h ← intro n,
--          return (ns, h::hs)) <|> return (ns, hs)) (tac (ns, hs))) <|> return ([], []) in
-- match e with
-- | (expr.const _ _)   := go return
-- | (expr.local_const _ _ _ t) := collect_proofs_in t ctx (ns, hs)
-- | (expr.mvar _ _ t)  := collect_proofs_in t ctx (ns, hs)
-- | (expr.app f x)     :=
--   go (λ nh, collect_proofs_in f ctx nh >>= collect_proofs_in x ctx)
-- | (expr.lam n b d e) :=
--   go (λ nh, do
--     nh ← collect_proofs_in d ctx nh,
--     var ← mk_local' n b d,
--     collect_proofs_in (expr.instantiate_var e var) (var::ctx) nh)
-- | (expr.pi n b d e) := do
--   nh ← collect_proofs_in d ctx (ns, hs),
--   var ← mk_local' n b d,
--   collect_proofs_in (expr.instantiate_var e var) (var::ctx) nh
-- | (expr.elet n t d e) :=
--   go (λ nh, do
--     nh ← collect_proofs_in t ctx nh,
--     nh ← collect_proofs_in d ctx nh,
--     collect_proofs_in (expr.instantiate_var e d) ctx nh)
-- | (expr.macro m l) :=
--   go (λ nh, mfoldl (λ x e, collect_proofs_in e ctx x) nh l)
-- | _                  := return (ns, hs)
-- end

example {α : Type*} [ring α] (f : Π a : α, a ≠ 0 → α) (a b : α) (hb : b ≠ a) :
  f (b - a) (mt sub_eq_zero_iff_eq.1 hb) = 0 :=
begin
  generalize_proofs,

end

example {α : Type*} [ring α] (f : Π a : α, a ≠ 0 → α) (b : α ) (hb : b ≠ 0) :
  f b hb = 0 :=
begin
  generalize_proofs,

end

#exit
import data.set.basic data.set.lattice
import data.equiv.basic

structure partition (α : Type) :=
(C : set (set α))
(non_empty : ∀ c ∈ C, ∃ a : α, a ∈ c)
(disjoint : ∀ c d ∈ C, (∃ x, x ∈ c ∩ d) → c = d)
(all : ⋃₀ C = set.univ)

variable {α : Type}

definition partitions_equiv_relns :
{r : α → α → Prop | equivalence r} ≃ partition α :=
{ to_fun := λ r, ⟨⋃ a : α, {{b : α | r.1 a b}},
    λ c ⟨s, ⟨a, ha⟩, m⟩, ⟨a,
      by simp only [ha.symm, set.mem_singleton_iff] at m;
        rw m; exact r.2.1 a⟩,
    λ u v ⟨s, ⟨a, ha⟩, m⟩ ⟨t, ⟨b, hb⟩, n⟩ ⟨c, hc⟩, begin
      clear _fun_match _x _fun_match _x _fun_match _x,
      simp [hb.symm, ha.symm] at *,
      simp [m, n] at *,
      have := r.2.2.2 hc.1 (r.2.2.1 hc.2),
      exact set.ext (λ x, ⟨r.2.2.2 (r.2.2.1 this), r.2.2.2 this⟩),
    end,
    set.eq_univ_of_forall $ λ a, ⟨{b : α | r.val a b}, set.mem_Union.2 ⟨a, by simp⟩, r.2.1 a⟩⟩,
  inv_fun := λ p, ⟨λ a b, ∃ s ∈ p.1, a ∈ s ∧ b ∈ s,
    ⟨λ a, let ⟨s, hs⟩ := set.eq_univ_iff_forall.1 p.4 a in
      ⟨s, by tauto⟩,
    λ a b, by simp only [and.comm, imp_self],
    λ a b c ⟨s, hs₁, hs₂⟩ ⟨t, ht₁, ht₂⟩,
      ⟨s, hs₁, hs₂.1, have t = s, from p.3 _ _ ht₁ hs₁ ⟨b, ht₂.1, hs₂.2⟩, this ▸ ht₂.2⟩⟩⟩,
  left_inv := λ ⟨r, hr⟩, subtype.eq begin
        ext x y,
        exact ⟨λ ⟨s, ⟨a, ⟨b, hb⟩, m⟩, t, ht⟩, begin simp [hb.symm] at *, simp [m] at *,
          exact hr.2.2 (hr.2.1 t) ht, end,
      λ h, ⟨{b : α | r x b}, set.mem_Union.2 ⟨x, by simp⟩,
        by simp [*, hr.1 x] at *⟩⟩
    end,
  right_inv := λ ⟨C, hc₁, hc₂, hc₃⟩, partition.mk.inj_eq.mpr $
    set.ext $ λ s, begin

    end }


#exit
import analysis.topology.topological_space

open filter

variables {α : Type*} [topological_space α]

def X : filter α := generate {s | compact (-s)}

lemma tendsto_X_right {α β : Type*} [topological_space β] (f : filter α) (m : α → β) :
  tendsto m f X ↔ ∀ s, compact (-s) → m ⁻¹' s ∈ f.sets :=
by simp [X, tendsto, sets_iff_generate, map, set.subset_def]

lemma mem_generate_iff {s : set (set α)} (hs : ∀ u v, u ∈ s → v ∈ s → u ∩ v ∈ s) {t : set α} :
  t ∈ (generate s).sets ↔ ∃ u ∈ s, s ⊆ u :=
begin


end

lemma tendsto_X_left {α β : Type*} [topological_space α]
  [topological_space β] (m : α → β) : tendsto m X X :=
begin
  rw [tendsto_X_right, X],

end

#exit

instance : preorder ℂ :=
{ le := λ x y, x.abs ≤ y.abs,
  le_refl := λ x, le_refl x.abs,
  le_trans := λ x y z, @le_trans ℝ _ _ _ _ }
#print filter
example (f : ℂ → ℂ) : tendsto f at_top at_top ↔
  ∀ x : ℝ, ∃ r, ∀ z : ℂ, r < z.abs → x < (f z).abs

#exit
import data.zmod.basic

def dihedral (n : ℕ+) := units ℤ × zmod n

variable (n : ℕ+)

def mul : Π (x y : dihedral n), dihedral n
| ⟨ff, x⟩ ⟨ff, y⟩ :=


#exit
import tactic.interactive -- to get simpa

namespace random

open nat
set_option trace.simplify.rewrite true
@[semireducible] theorem add_right_cancel (n m k : nat) : n + k = m + k → n = m :=
begin
  induction k with k ih,
  { -- base case
    exact id, -- n = n + 0 is true by definition
  },
  { -- inductive step
    show succ (n + k) = succ (m + k) → _, -- again true by definition
    intro H,
    apply ih,
    injection H,
  }
end
#print axioms add_right_cancel

end random

#exit
universe u

@[derive decidable_eq] inductive poly_aux : Type
| zero : poly_aux
| X : poly_aux
| C : poly_aux

inductive polynomial_aux {α : Type u} [comm_semiring α] : poly_aux → Type u
| zero : polynomial_aux poly_aux.zero
| X : polynomial_aux poly_aux.X ⊕ polynomial_aux poly_aux.C → polynomial_aux poly_aux.X
| C {a : α} (h : a ≠ 0) : polynomial_aux poly_aux.zero ⊕ polynomial_aux poly_aux.X →
  polynomial_aux poly_aux.C

#exit
import analysis.metric_space

open set

set_option trace.simplify.rewrite true

lemma closed_ball_Icc {x r : ℝ} : closed_ball x r = Icc (x-r) (x+r) :=
by simp only [closed_ball, Icc, dist, abs_sub_le_iff,
  sub_le_iff_le_add', and.comm, add_comm]

#print closed_ball_Icc

#exit
import ring_theory.determinant data.polynomial
open polynomial
def M : matrix (unit) (unit) (polynomial ℤ) :=
λ r c, if r = 0 then if c = 1 then 1 else -1
  else if c = 0 then 0
  else if c = 1 then if r = 1 then -4 else -3
  else if r = 2 then 5 else 6

#exit
import algebra.archimedean
import data.real.basic

definition completeness_axiom (k : Type*) [preorder k] : Prop :=
∀ (S : set k), (∃ x, x ∈ S) → (∃ x, ∀ y ∈ S, y ≤ x) →
  ∃ x, ∀ y, x ≤ y ↔ ∀ z ∈ S, z ≤ y

lemma reals_complete : completeness_axiom ℝ :=
λ S hS₁ hS₂, ⟨real.Sup S, λ y, ⟨λ h z hz, le_trans (real.le_Sup S hS₂ hz) h,
  λ h, (real.Sup_le _ hS₁ hS₂).2 h⟩⟩

open function
section

parameters {K : Type*} {L : Type*} [discrete_linear_ordered_field K] [archimedean K]
  [discrete_linear_ordered_field L] [archimedean L] (hL : completeness_axiom L)

lemma f_exists (k : K) :
  ∃ x, ∀ y, x ≤ y ↔ ∀ z ∈ (rat.cast '' {q : ℚ | (q : K) ≤ k} : set L), z ≤ y :=
(hL (rat.cast '' {q : ℚ | (q : K) ≤ k})
  (let ⟨q, hq⟩ := exists_rat_lt k in ⟨q, ⟨q, ⟨le_of_lt hq, rfl⟩⟩⟩)
  (let ⟨q, hq⟩ := exists_rat_gt k in ⟨q, λ y ⟨g, hg⟩, hg.2 ▸ rat.cast_le.2 $
    (@rat.cast_le K _ _ _).1 (le_trans hg.1 (le_of_lt hq))⟩))

noncomputable def f (k : K) : L :=
classical.some (f_exists k)

lemma f_le_iff {q : ℚ} {k : K} : f k ≤ q ↔ k ≤ q :=
have ∀ (y : L), f k ≤ y ↔ ∀ (z : L), z ∈ rat.cast '' {q : ℚ | ↑q ≤ k} → z ≤ y,
    from classical.some_spec (f_exists k),
by rw this q; exact
  ⟨λ h, le_of_not_gt (λ h1, let ⟨r, hr⟩ := exists_rat_btwn h1 in
      not_le_of_gt hr.1 (rat.cast_le.2 (rat.cast_le.1 (h _ ⟨r, ⟨le_of_lt hr.2, rfl⟩⟩)))),
    λ h z ⟨g, hg⟩, hg.2 ▸ rat.cast_le.2 (rat.cast_le.1 (le_trans hg.1 h))⟩

lemma lt_f_iff {q : ℚ} {k : K} : (q : L) < f k ↔ (q : K) < k :=
by rw [← not_le, ← not_le, f_le_iff]

lemma le_f_iff {q : ℚ} {k : K} : (q : L) ≤ f k ↔ (q : K) ≤ k :=
⟨λ h, le_of_not_gt $ λ hk,
  let ⟨r, hr⟩ := exists_rat_btwn hk in
  not_lt_of_ge (f_le_iff.2 (le_of_lt hk))
    (lt_of_le_of_ne h (λ hq,
      by rw [rat.cast_lt, ← @rat.cast_lt L, hq, lt_f_iff] at hr;
        exact not_lt_of_gt hr.1 hr.2)),
  λ h, le_of_not_gt $ λ hk,
    let ⟨r, hr⟩ := exists_rat_btwn hk in
    not_lt_of_ge h $ lt_of_le_of_lt (f_le_iff.1 (le_of_lt hr.1))
        (rat.cast_lt.2 (rat.cast_lt.1 hr.2))⟩

lemma f_lt_iff {q : ℚ} {k : K} : f k < q ↔ k < q :=
by rw [← not_le, ← not_le, le_f_iff]

@[simp] lemma f_rat_cast (q : ℚ) : f q = q :=
le_antisymm (by rw f_le_iff) (by rw le_f_iff)

lemma f_injective : function.injective f :=
λ x y hxy, match lt_trichotomy x y with
| (or.inl h) := let ⟨q, hq⟩ := exists_rat_btwn h in
  by rw [← lt_f_iff, ← f_lt_iff] at hq;
    exact absurd hxy (ne_of_lt (lt_trans hq.1 hq.2))
| (or.inr (or.inl h)) := h
| (or.inr (or.inr h)) := let ⟨q, hq⟩ := exists_rat_btwn h in
  by rw [← lt_f_iff, ← f_lt_iff] at hq;
    exact absurd hxy.symm (ne_of_lt (lt_trans hq.1 hq.2))
end

lemma f_is_ring_hom : is_ring_hom f :=
⟨by rw [← rat.cast_one, f_rat_cast, rat.cast_one],
  λ x y, le_antisymm _ _,
  λ x y, le_antisymm
    (f_le_iff.2 _)
    _⟩

theorem characterisation_of_reals :
  ∃ f : K → ℝ, is_ring_hom f ∧ bijective f ∧ ∀ x y : K, x < y → f x < f y :=

end
#exit
import data.fintype

theorem Q0505 :
  ¬ (∃ a b c : ℕ, 6 * a + 9 * b + 20 * c = 43)
  ∧ ∀ m, m > 43 → ∃ a b c : ℕ, 6 * a + 9 * b + 20 * c = m :=


#exit
import data.nat.choose

open finset nat

theorem Q0403 : ∀ n : ℕ, finset.sum (finset.range n.succ)
  (λ i, (-1 : ℤ) ^ i * choose (2 * n) (2 * i)) = -2 ^ n
| 0 := rfl
| (n+1) := begin
  rw [sum_range_succ', function.comp],
  conv in (choose (2 * (n + 1)) (2 * succ _))
  { rw [mul_add, mul_succ, mul_zero, zero_add, mul_succ,
    choose_succ_succ, choose_succ_succ, choose_succ_succ],  },
  simp [sum_add_distrib, mul_add, *, -range_succ]
end

theorem Q0403 : finset.sum (finset.range 51)
  (λ i, (-1 : ℤ) ^ i * choose 100 (2 * i)) = 0 := sorry



def Fin : nat → Type
  | 0 := empty
  | (n+1) := option (Fin n)

inductive tm  : nat -> Type
  | var_tm : Π {ntm : nat}, Fin ntm -> tm ntm
  | app : Π {ntm : nat}, tm ntm -> tm ntm -> tm ntm
  | lam : Π {ntm : nat}, tm (nat.succ ntm) -> tm ntm

open tm

inductive type : Type
| tint : type
| tarrow : type → type → type

definition empty_ctx : Fin 0 → type.

local infix `⤏`:20 := type.tarrow

inductive types : Π{m : ℕ}, (Fin m → type) → tm m → type → Prop
| tvar {m} Γ (x : Fin m) : types Γ (var_tm x) (Γ x)
| tapp {m} Γ (e₁ : tm m) e₂ (A B) : types Γ e₁ (A ⤏ B) → types Γ e₂ A → types Γ (app e₁ e₂) B
-- | tlam {m} Γ (e : tm (nat.succ m)) (A B) : types (@scons _ m  A Γ) e B → types Γ (lam e) (A ⤏ B) requires some more definitions
def step {n} (t t' : tm n) := tt. --(..)
#print types.drec_on

lemma preservation (A : type) {n} (ctx : Fin n → type) (e₁ : tm 0) :
  types empty_ctx e₁ A →
      forall e₂, step e₁ e₂ → types empty_ctx e₂ A :=
λ H₁ e H₂,
begin
  destruct H₁, dsimp,
  exact sorry, exact sorry,

end


#print preservation
set_option trace.check true
lemma preservation (A : type) {n} (ctx : Fin n → type) (e₁ : tm 0) :
  types empty_ctx e₁ A →
      forall e₂, step e₁ e₂ → types empty_ctx e₂ A :=
λ H₁, @types.rec_on
  (λ m ctx e₁ t, m = 0 → ctx == empty_ctx → ∀ e₂ : tm m, step e₁ e₂ → types ctx e₂ A) 0 empty_ctx e₁ A H₁
    begin
      intros m Γ _ hm hΓ,
      subst hm,
      have := eq_of_heq hΓ,
      subst this,

    end sorry rfl (heq.refl _)

set_option trace.check true

lemma preservation1 (A : type) {n} (ctx : Fin n → type) (e₁ : tm 0) :
  types empty_ctx e₁ A →
      forall e₂, step e₁ e₂ → types empty_ctx e₂ A :=
begin
  intros H₁,
  induction H₁,


end

#print empty_ctx
def f : ℕ+ → ℕ+
| ⟨1, h⟩  :=

example (x y : ℕ ): (x + y) * 2 = sorry :=
begin
  simp [mul_comm],


end

example : real.partial_order = (@semilattice_inf.to_partial_order ℝ
       (@lattice.to_semilattice_inf ℝ
          (@conditionally_complete_lattice.to_lattice ℝ
             (@conditionally_complete_linear_order.to_conditionally_complete_lattice ℝ
                real.lattice.conditionally_complete_linear_order)))) := rfl

#print orderable_topology
#eval let n := 3 in let r := 2 in
  (fintype.card {f : fin r → fin n // function.injective f},
    fintype.card {f : fin n → fin r // function.surjective f})

#eval 93 / 3

#eval 2 ^ 5 - 2 * (1 ^ 5)

#eval 3 ^ 5 - 3 * (2 ^ 5 - (1 ^ 5))

#eval

#eval choose 5 2

#exit
import data.set.basic

class has_heart (α : Type*) := (heart : α → α → Prop)

notation a ` ♥ ` b := has_heart.heart a b

variables {α : Type*} [has_heart α]
def upper_bounds (s : set α) : set α := { x | ∀a ∈ s, a ♥ x }
def lower_bounds (s : set α) : set α := { x | ∀a ∈ s, x ♥ a }
def is_least (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ lower_bounds s
def is_greatest (s : set α) (a : α) : Prop := a ∈ s ∧ a ∈ upper_bounds s
def is_lub (s : set α) : α → Prop := is_least (upper_bounds s)
def is_glb (s : set α) : α → Prop := is_greatest (lower_bounds s)

theorem warm_up (S : Type) [has_heart S] :
  (∀ E : set S, (∃ a, a ∈ E) ∧ (∃ b, b ∈ upper_bounds E) → ∃ s : S, is_lub E s) →
  (∀ E : set S, (∃ a, a ∈ E) ∧ (∃ b, b ∈ lower_bounds E) → ∃ s : S, is_glb E s) :=
λ h E ⟨⟨e, he⟩, ⟨b, hb⟩⟩, let ⟨s, hs⟩ := h (lower_bounds E) ⟨⟨b, hb⟩, ⟨e, λ a ha, ha e he⟩⟩ in
  ⟨s, ⟨λ a ha, hs.2 _ (λ c hc, hc _ ha), hs.1⟩⟩

#print warm_up

#exit
import data.real.basic

structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

protected definition add : ℂ → ℂ → ℂ
| ⟨a, b⟩ ⟨c, d⟩ := ⟨a + c, b + d⟩
#print tactic.simp_config
notation a `+` b := complex.add a b
set_option trace.simplify.rewrite true
protected lemma add_assoc' (z1 z2 z3 : ℂ) : z1 + z2 + z3 = z1 + (z2 + z3) :=
begin
  cases z1 with x1 y1, cases z2 with x2 y2, cases z3 with x3 y3,
  simp only [complex.add, add_assoc],
  exact ⟨rfl, rfl⟩
end

#print complex.add_assoc'

end complex


#exit
import data.fintype.basic group_theory.order_of_element algebra.pi_instances

variables {α : Type*} [fintype α] [decidable_eq α]

instance [group α] : decidable (∃ a : α, ∀ b : α, b ∈ gpowers a) :=
@fintype.decidable_exists_fintype α _ (λ a, ∀ b, b ∈ gpowers a)
  (λ a, @fintype.decidable_forall_fintype α _ (λ b, b ∈ gpowers a)
    (decidable_gpowers))

instance [group α] : decidable (is_cyclic α) :=



#exit
import data.rat.basic

inductive real : bool → Type
| of_rat : ℚ → real tt
| limit (x : Π q : ℚ, 0 < q → real tt) (∀ δ ε : ℚ, 0 < δ → 0 < ε → real ff ) :

mutual inductive A, B
with A : Type
| mk : B → A
with B : Type
| mk : A → B



def A.to_sort (l : Sort*) : A → l
| (A.mk (B.mk x)) := A.to_sort x

#print A.rec

def AB.reca : Π {Ca : A → Sort*}
  (ha : Π a : A, Ca a → Cb (B.mk a))
  (a : A), Ca a := λ _ _ _ _ a, A.to_sort _ a

def A.to_false (a : A) : false :=
AB.reca _ _ _

#print A.to_sort._main._pack
#exit
import data.finset analysis.metric_space

#print tactic.interactive.dsimp


example {α : Type*} (s : finset α) : s.card = 1 → {a : α // s = finset.singleton a} :=
finset.rec_on s (λ s, @quotient.rec_on_subsingleton _ _
  (λ t : multiset α, Π (nodup : multiset.nodup t),
    finset.card {val := t, nodup := nodup} = 1 → {a // finset.mk t nodup = finset.singleton a})
      (λ l, ⟨λ a b, funext (λ x, funext (λ y, subtype.eq $ finset.singleton_inj.1 $
        by rw [← (a x y).2, ← (b x y).2]))⟩) s
  (λ l, list.rec_on l (λ _ h, nat.no_confusion h)
    (λ a l _ _ h, have l.length = 0, from nat.succ_inj h,
      ⟨a, finset.eq_of_veq $ by dsimp; rw [list.length_eq_zero.1 this]; refl⟩)) )

#eval g ({1} : finset ℕ) rfl
#print metric_space
mutual inductive A, B
with A : Type
| mk : B → A
with B : Type
| mk : A → B

def size : A ⊕ B → ℕ
|

inductive AB : bool → Type
| mk_0 : AB ff → AB tt
| mk_1 : AB tt → AB ff

example (b : bool) (x : AB b) : false :=
AB.rec_on x (λ _, id) (λ _, id)

lemma A_mut_false(x : psum unit unit) (a : A._mut_ x) : false :=
  A._mut_.rec_on a (λ _, id) (λ _, id)

lemma h : A ⊕ B → false
| (sum.inl (A.mk b)) := h (sum.inr b)
| (sum.inr (B.mk a)) := h (sum.inl a)


example : A → false := h ∘ sum.inl

example : B → false := h ∘ sum.inr

#print prefix A
#print B
#print A._mut_

#exit
import analysis.exponential
#print quot.rec_on
universes u v
variable {α : Sort u}
variable {r : α → α → Prop}
variable {β : quot r → Sort v}
open quot
local notation `⟦`:max a `⟧` := quot.mk r a
attribute [simp] mul_comm


inductive Id {α : Type} (a : α) : α → Type
| refl : Id a

inductive Id2 {α : Type} : α → α → Type
| refl : Π a : α, Id2 a a

inductive eq2 {α : Type} : α → α → Prop
| refl : ∀ a : α, eq2 a a

lemma eq2_iff_eq {α : Type} (a b : α) : eq2 a b ↔ a = b :=
⟨λ h, eq2.rec (λ _, rfl) h, λ h, eq.rec (eq2.refl _) h⟩
universe l
example : Π {α : Type} {a b : α} {C : Id a b → Sort l},
  C (Id.refl a) → Π {a_1 : α} (n : Id a a_1), C a_1 n

#print Id.rec
#print eq.rec
#print Id2.rec
#print eq2.rec

local attribute [instance] classical.prop_decidable

example (α β : Type*) : ((α → β) → α) → α :=
if h : nonempty α then λ _, classical.choice h
else (λ f, f (λ a, (h ⟨a⟩).elim))


noncomputable example (α : Type*) : α ⊕ (α → empty) :=
if h : nonempty α then sum.inl (classical.choice h)
else sum.inr (λ a, (h ⟨a⟩).elim)

#print quot.ind
#print quot.rec
#print quot.lift
example : ∀ {α : Sort u} {r : α → α → Prop} {β : quot r → Prop},
  (∀ (a : α), β (mk r a)) → ∀ (q : quot r), β q :=
λ α r β f q, quot.rec f (λ _ _ _, rfl) q
set_option pp.proofs true
example : Π {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β),
  (∀ (a b : α), r a b → f a = f b) → quot r → β := λ α r β f h q,
  @quot.rec α r (λ _, β) f
  (λ a b hab, eq_of_heq (eq_rec_heq _ begin  end))

protected lemma lift_indep_pr1
  (f : Π a, β ⟦a⟧) (h : ∀ (a b : α) (p : r a b), (eq.rec (f a) (sound p) : β ⟦b⟧) = f b)
  (q : quot r) : (lift (quot.indep f) (quot.indep_coherent f h) q).1 = q :=
quot.ind (by)

#exit
import analysis.topology.continuity data.zmod.basic
universe u
class t2_space1 (α : Type u) [topological_space α] : Prop :=
(t2 : ∀x y, x ≠ y → ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅)

class t2_space2 (α : Type u) [topological_space α] : Prop :=
(t2 : ∀x y, (∀u v : set α, is_open u → is_open v → x ∈ u → y ∈ v → ∃ r, r ∈ u ∩ v) → x = y)



import data.fintype

open equiv

instance thing {α β : Type*} [group α] [group β] [fintype α] [decidable_eq β] :
  decidable_pred (@is_group_hom α β _ _) :=
λ f, decidable_of_iff (∀ x y, f (x * y) = f x * f y)
⟨λ h, ⟨h⟩, λ ⟨h⟩, h⟩

lemma h : ¬is_group_hom ((^3) : perm (fin 4) → perm (fin 4)) := dec_trivial

#print fintype.equiv_fin

#eval list.find (λ x : perm (fin 4) × perm (fin 4),
  x.1 ^ 3 * x.2 ^ 3 ≠ (x.1 * x.2) ^ 3) (quot.unquot
  (finset.univ : finset (perm (fin 4) × perm (fin 4))).1)

#print h

#exit

class is_rat (x : ℝ) :=
(val : ℚ)
(val_eq : (val : ℝ) = x)

variables (x y : ℝ) [is_rat x] [is_rat y]
noncomputable theory

instance : is_rat (x + y) := ⟨is_rat.val x + is_rat.val y, by simp [is_rat.val_eq]⟩
instance : is_rat (x * y) := ⟨is_rat.val x * is_rat.val y, by simp [is_rat.val_eq]⟩
instance : is_rat (-x) := ⟨-is_rat.val x, by simp [is_rat.val_eq]⟩
instance : is_rat (x - y) := ⟨is_rat.val x - is_rat.val y, by simp [is_rat.val_eq]⟩
instance : is_rat (x / y) := ⟨is_rat.val x / is_rat.val y, by simp [is_rat.val_eq]⟩
instance : is_rat (x⁻¹) := ⟨(is_rat.val x)⁻¹, by simp [is_rat.val_eq]⟩
instance zero_is_rat : is_rat 0 := ⟨0, by simp [rat.cast_zero]⟩
instance one_is_rat : is_rat 1 := ⟨1, by simp⟩
instance : is_rat (bit0 x) := by unfold bit0; apply_instance
instance : is_rat (bit1 x) := by unfold bit1; apply_instance
instance i2 : decidable (x = y) :=
by rw [← is_rat.val_eq x, ← is_rat.val_eq y, rat.cast_inj]; apply_instance
instance i3 : decidable (x ≤ y) :=
by rw [← is_rat.val_eq x, ← is_rat.val_eq y, rat.cast_le]; apply_instance
instance i4 : decidable (x < y) :=
by rw [← is_rat.val_eq x, ← is_rat.val_eq y, rat.cast_lt]; apply_instance

lemma is_rat.val_inj {x y : ℝ} [is_rat x] [is_rat y] (h : is_rat.val x = is_rat.val y) : x = y :=
(is_rat.val_eq x).symm.trans (eq.trans (rat.cast_inj.2 h) (is_rat.val_eq y))
a ^ 2 + 3 * a - 1 = 0 ↔ (X ^ 2 + 3 * X - 1).eval a = 0
set_option profiler true
set_option class.instance_max_depth 100
instance i5 : is_rat ((5 : ℝ) / 4) := by apply_instance
#print as_true

#eval ( (5 : ℝ) * 4 = 10 * 2 : bool)

example : (5 : ℚ) / 2 = 10 / 4 := rfl
lemma l1 : (5 : ℝ) / 2 = 10 / 4 := is_rat.val_inj rfl



#print l1
#print l2

#exit

#exit
#print expr
open expr level
#print level
meta def level.repr : level → string
| zero       := "0"
| (succ l)   := level.repr l ++ "+1"
| (max a b)  := "max " ++ a.repr ++ " " ++ b.repr
| (imax a b) := "imax " ++ a.repr ++ " " ++ b.repr
| (param a)  := "param " ++ a.to_string
| (mvar a)   := "mvar " ++ a.to_string

meta instance : has_repr level := ⟨level.repr⟩

meta def expr.to_string' : expr → string
| (var a) := "var (" ++ repr a ++")"
| (sort a) := "sort (" ++ repr a ++")"
| (const a b) := "const (" ++ a.to_string ++ ") (" ++ repr b ++")"
| (expr.mvar a b c) := "mvar (" ++ a.to_string ++ ") (" ++ b.to_string ++ ")"
| (local_const a b c d) := "local_const (" ++ a.to_string ++ ") (" ++ b.to_string ++ ") (" ++
   expr.to_string' d ++")"
| (pi a b c d) := "pi (" ++ a.to_string ++") (" ++ expr.to_string' c  ++") (" ++ expr.to_string' d ++")"
| (lam a b c d) := "lam (" ++ a.to_string ++ ") (" ++ expr.to_string' c ++ ") (" ++ expr.to_string' d ++")"
| (app a b) := "app (" ++ expr.to_string' a ++ ") (" ++ expr.to_string b ++ ")"
| _ := "aargh"

def list.nil' : Π (α : Type), list α := @list.nil

def f : ℕ → ℕ := id

meta def x : tactic unit :=
do t ← tactic.infer_type `(f),
  tactic.trace (expr.to_string' t), tactic.skip

#eval (format.compose (format.of_string "a") (format.of_string "b")).to_string
#print expr.to_raw_fmt
#eval (`(fin) : expr).to_raw_fmt.to_string
#eval expr.to_string' `(fin)

#exit
import data.equiv.encodable algebra.group_power
#print encodable

-- #eval encodable.choose (show ∃ x : (ℤ × ℕ), x.1 ^ 2 + 615 = 2 ^ x.2, from ⟨(59, 12), rfl⟩)

#print tactic.interactive.rw
#print tactic.transparency
example : 2 = 1 + 1 := by tactic.reflexivity tactic.transparency.none
#print tactic.interactive.refl
example : 2 = list.sum [2] := by tactic.reflexivity tactic.transparency.semireducible

#exit
import data.polynomial
open polynomial
#eval (X ^ 2 + 3 * X - 4 : polynomial ℤ).comp (X ^ 3 - X)


example : (@with_top.add_monoid ℕ _) = (@add_comm_monoid.to_add_monoid (with_top ℕ) _) := rfl

variables {α β γ δ : Type} {f : α → β}

#check function.comp (@function.comp ℕ _ _) (@function.comp ℕ ℕ (ℕ → ℕ))
#check
#print infer_instance
@[derive decidable_eq] inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:51 := fml.not

inductive prf : fml → Type
| axk {p q} : prf (p →' q →' p)
| axs {p q r} : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX {p q} : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

instance (p): has_sizeof (prf p) := by apply_instance

open prf

meta def length {f : fml} (t : prf f) : ℕ :=
prf.rec_on t (λ _ _, 1) (λ _ _ _, 1) (λ _ _, 1) (λ _ _ _ _, (+))

instance (p q : fml) : has_coe_to_fun (prf (p →' q)) :=
{ F := λ x, prf p → prf q,
  coe := λ x y, mp y x }

lemma imp_self' (p : fml) : prf (p →' p) :=
mp (@axk p p) (mp axk axs)

lemma imp_comm {p q r : fml} (h : prf (p →' q →' r)) : prf (q →' p →' r) :=
mp axk (mp (mp (mp h axs) axk) (@axs _ (p →' q) _))

lemma imp_of_true (p : fml) {q : fml} (h : prf q) : prf (p →' q) :=
mp h axk

namespace prf
prefix `⊢ `:30 := prf

def mp' {p q} (h1 : ⊢ p →' q) (h2 : ⊢ p) : ⊢ q := mp h2 h1
def a1i {p q} : ⊢ p → ⊢ q →' p := mp' axk
def a2i {p q r} : ⊢ p →' q →' r → ⊢ (p →' q) →' p →' r := mp' axs
def con4i {p q} : ⊢ ¬' p →' ¬' q → ⊢ q →' p := mp' axX
def mpd {p q r} (h : ⊢ p →' q →' r) : ⊢ p →' q → ⊢ p →' r := mp' (a2i h)
def syl {p q r} (h1 : ⊢ p →' q) (h2 : ⊢ q →' r) : ⊢ p →' r := mpd (a1i h2) h1
def id {p} : ⊢ p →' p := mpd axk (@axk p p)
def a1d {p q r} (h : ⊢ p →' q) : ⊢ p →' r →' q := syl h axk
def com12 {p q r} (h : ⊢ p →' q →' r) : ⊢ q →' p →' r := syl (a1d id) (a2i h)
def con4d {p q r} (h : ⊢ p →' ¬' q →' ¬' r) : ⊢ p →' r →' q := syl h axX
def absurd {p q} : ⊢ ¬' p →' p →' q := con4d axk
def imidm {p q} (h : ⊢ p →' p →' q) : ⊢ p →' q := mpd h id
def contra {p} : ⊢ (¬' p →' p) →' p := imidm (con4d (a2i absurd))
def notnot2 {p} : ⊢ ¬' ¬' p →' p := syl absurd contra
def mpdd {p q r s} (h : ⊢ p →' q →' r →' s) : ⊢ p →' q →' r → ⊢ p →' q →' s := mpd (syl h axs)
def syld {p q r s} (h1 : ⊢ p →' q →' r) (h2 : ⊢ p →' r →' s) : ⊢ p →' q →' s := mpdd (a1d h2) h1
def con2d {p q r} (h1 : ⊢ p →' q →' ¬' r) : ⊢ p →' r →' ¬' q := con4d (syld (a1i notnot2) h1)
def con2i {p q} (h1 : ⊢ p →' ¬' q) : ⊢ q →' ¬' p := con4i (syl notnot2 h1)
def notnot1 {p} : ⊢ p →' ¬' ¬' p := con2i id
#eval length (@notnot1 (atom 0))

lemma notnot1' {p} : ⊢ p →' ¬' ¬' p :=
mp (mp (mp (mp axk (mp (mp axX axk) axs))
  (mp (mp (mp (mp axk (mp axk axs))
  (mp (mp (mp (mp axk (mp (mp axX axk) axs)) axs) (mp (mp axX axk) axs)) axs)) axk) axs))
     (mp (mp (mp axk (mp axk axs)) axk) axs)) axX

-- @mp ((¬' ¬' ¬' p) →' ¬' p) (p →' ¬' ¬' p)
--     (@mp ((¬' ¬' ¬' p) →' (¬' p) →' (¬' p) →' ¬' p) ((¬' ¬' ¬' p) →' ¬' p)
--        (@mp ((¬' p) →' (¬' p) →' ¬' p) ((¬' ¬' ¬' p) →' (¬' p) →' (¬' p) →' ¬' p)
--           (@axk (¬' p) (¬' p))
--           (@axk ((¬' p) →' (¬' p) →' ¬' p) (¬' ¬' ¬' p)))
--        (@mp ((¬' ¬' ¬' p) →' ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--           (((¬' ¬' ¬' p) →' (¬' p) →' (¬' p) →' ¬' p) →' (¬' ¬' ¬' p) →' ¬' p)
--           (@mp ((¬' ¬' ¬' p) →' (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--              ((¬' ¬' ¬' p) →' ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--              (@mp ((¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                 ((¬' ¬' ¬' p) →' (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                 (@mp ((¬' ¬' ¬' p) →' ¬' ¬' ¬' p)
--                    ((¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                    (@mp ((¬' ¬' ¬' p) →' (¬' ¬' ¬' p) →' ¬' ¬' ¬' p) ((¬' ¬' ¬' p) →' ¬' ¬' ¬' p)
--                       (@axk (¬' ¬' ¬' p) (¬' ¬' ¬' p))
--                       (@mp ((¬' ¬' ¬' p) →' ((¬' ¬' ¬' p) →' ¬' ¬' ¬' p) →' ¬' ¬' ¬' p)
--                          (((¬' ¬' ¬' p) →' (¬' ¬' ¬' p) →' ¬' ¬' ¬' p) →'
--                             (¬' ¬' ¬' p) →' ¬' ¬' ¬' p)
--                          (@axk (¬' ¬' ¬' p) ((¬' ¬' ¬' p) →' ¬' ¬' ¬' p))
--                          (@axs (¬' ¬' ¬' p) ((¬' ¬' ¬' p) →' ¬' ¬' ¬' p) (¬' ¬' ¬' p))))
--                    (@mp
--                       ((¬' ¬' ¬' p) →'
--                          (¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                       (((¬' ¬' ¬' p) →' ¬' ¬' ¬' p) →'
--                          (¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                       (@mp ((¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                          ((¬' ¬' ¬' p) →'
--                             (¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                          (@axk (¬' ¬' ¬' p) (¬' ¬' (¬' p) →' (¬' p) →' ¬' p))
--                          (@axk ((¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                             (¬' ¬' ¬' p)))
--                       (@axs (¬' ¬' ¬' p) (¬' ¬' ¬' p)
--                          ((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p))))
--                 (@mp
--                    ((¬' ¬' ¬' p) →'
--                       ((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p) →'
--                         (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                    (((¬' ¬' ¬' p) →' (¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p) →'
--                       (¬' ¬' ¬' p) →' (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                    (@mp
--                       (((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p) →'
--                          (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                       ((¬' ¬' ¬' p) →'
--                          ((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p) →'
--                            (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                       (@axX (¬' ¬' p) (¬' (¬' p) →' (¬' p) →' ¬' p))
--                       (@axk
--                          (((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p) →'
--                             (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                          (¬' ¬' ¬' p)))
--                    (@axs (¬' ¬' ¬' p) ((¬' ¬' (¬' p) →' (¬' p) →' ¬' p) →' ¬' ¬' ¬' p)
--                       ((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p))))
--              (@mp
--                 ((¬' ¬' ¬' p) →'
--                    ((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p) →'
--                      ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--                 (((¬' ¬' ¬' p) →' (¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p) →'
--                    (¬' ¬' ¬' p) →' ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--                 (@mp
--                    (((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p) →'
--                       ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--                    ((¬' ¬' ¬' p) →'
--                       ((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p) →'
--                         ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--                    (@axX ((¬' p) →' (¬' p) →' ¬' p) (¬' p))
--                    (@axk
--                       (((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p) →'
--                          ((¬' p) →' (¬' p) →' ¬' p) →' ¬' p)
--                       (¬' ¬' ¬' p)))
--                 (@axs (¬' ¬' ¬' p) ((¬' ¬' p) →' ¬' (¬' p) →' (¬' p) →' ¬' p)
--                    (((¬' p) →' (¬' p) →' ¬' p) →' ¬' p))))
--           (@axs (¬' ¬' ¬' p) ((¬' p) →' (¬' p) →' ¬' p) (¬' p))))
--     (@axX p (¬' ¬' p))

-- set_option pp.implicit true

#print not_not_p_of_p

-- /-
-- example usage:
-- lemma p_of_p_of_p_of_q (p q : fml) : prf $ (p →' q) →' (p →' p) :=
-- begin
--   apply mp (p →' q →' p) ((p →' q) →' p →' p) (axk p q),
--   exact axs p q p
-- end
-- -/

-- theorem Q6b (p : fml) : prf $ p →' ¬' ¬' p := sorry

namespace prop_logic

-- infixr ` →' `:50 := imp
-- local notation ` ¬' ` := fml.not

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:51 := fml.not

--CAN I MAKE THIS A FUNCTION INTO PROP INSTEAD OF TYPE????
-- inductive thm : fml → Type
-- | axk (p q) : thm (p →' q →' p)
-- | axs (p q r) : thm $ (p →' q →' r) →' (p →' q) →' (p →' r)
-- | axn (p q) : thm $ ((¬' q) →' (¬' p)) →' p →' q
-- | mp {p q} : thm p → thm (p →' q) → thm q
-- open thm

lemma p_of_p (p : fml) : prf (p →' p) :=
mp (@axk p p) (mp axk axs)


inductive consequence (G : list fml) : fml → Type
| axk (p q) : consequence (p →' q →' p)
| axs (p q r) : consequence $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axn (p q) : consequence $ ((¬'q) →' (¬'p)) →' p →' q
| mp (p q) : consequence p → consequence (p →' q) → consequence q
| of_G (g ∈ G) : consequence g

lemma consequence_of_thm (f : fml) (H : prf f) (G : list fml) : consequence G f :=
begin
  induction H,
  exact consequence.axk G H_p H_q,
  exact consequence.axs G H_p H_q H_r,
  exact consequence.axn G H_p H_q,
  exact consequence.mp H_p H_q H_ih_a H_ih_a_1,
end

lemma thm_of_consequence_null (f : fml) (H : consequence [] f) : prf f :=
begin
  induction H,
  exact @axk H_p H_q,
  exact @axs H_p H_q H_r,
  exact @axX H_p H_q,
  exact mp H_ih_a H_ih_a_1,
  exact false.elim (list.not_mem_nil H_g H_H),
end

theorem deduction (G : list fml) (p q : fml) (H : consequence (p :: G) q) : consequence G (p →' q) :=
begin
  induction H,
  have H1 := consequence.axk G H_p H_q,
  have H2 := consequence.axk G (H_p →' H_q →' H_p) p,
  exact consequence.mp _ _ H1 H2,
  have H6 := consequence.axs G H_p H_q H_r,
  have H7 := consequence.axk G ((H_p →' H_q →' H_r) →' (H_p →' H_q) →' H_p →' H_r) p,
  exact consequence.mp _ _ H6 H7,
  have H8 := consequence.axn G H_p H_q,
  have H9 := consequence.axk G (((¬' H_q) →' ¬' H_p) →' H_p →' H_q) p,
  exact consequence.mp _ _ H8 H9,
  have H3 := consequence.axs G p H_p H_q,
  have H4 := consequence.mp _ _ H_ih_a_1 H3,
  exact consequence.mp _ _ H_ih_a H4,
  rw list.mem_cons_iff at H_H,
  exact if h : H_g ∈ G then
  begin
    have H51 := consequence.of_G H_g h,
    have H52 := consequence.axk G H_g p,
    exact consequence.mp _ _ H51 H52,
  end else
  begin
    have h := H_H.resolve_right h,
    rw h,
    exact consequence_of_thm _ (p_of_p p) G,
  end
end

lemma part1 (p : fml) : consequence [¬' (¬' p)] p :=
begin
  have H1 := consequence.axk [¬' (¬' p)] p p,
  have H2 := consequence.axk [¬' (¬' p)] (¬' (¬' p)) (¬' (¬' (p →' p →' p))),
  have H3 := consequence.of_G (¬' (¬' p)) (list.mem_singleton.2 rfl),
  have H4 := consequence.mp _ _ H3 H2,
  have H5 := consequence.axn [¬' (¬' p)] (¬' p) (¬' (p →' p →' p)),
  have H6 := consequence.mp _ _ H4 H5,
  have H7 := consequence.axn [¬' (¬' p)] (p →' p →' p) p,
  have H8 := consequence.mp _ _ H6 H7,
  exact consequence.mp _ _ H1 H8,
end

lemma part1' (p : fml) : prf (¬' ¬' p →' p) :=
begin
  have H1 := @axk p p,
  have H2 := @axk (¬' ¬' p) (¬' ¬' (p →' p →' p)),
  have H3 := imp_self' (¬' ¬' p),
  have H4 := mp H3 H2,

end

lemma p_of_not_not_p (p : fml) : thm ((¬' (¬' p)) →' p) :=
begin
  have H1 := deduction [] (¬' (¬' p)) p,

  have H2 := H1 (part1 p),
  exact thm_of_consequence_null ((¬' (¬' p)) →' p) H2,
end

theorem not_not_p_of_p (p : fml) : thm (p →' (¬' (¬' p))) :=
begin
  have H1 := thm.axn p (¬' (¬' p)),
  have H2 := p_of_not_not_p (¬' p),
  exact thm.mp H2 H1,
end
set_option pp.implicit true
#reduce not_not_p_of_p

theorem not_not_p_of_p' (p : fml) : thm (p →' (¬' (¬' p))) :=
thm.mp
    (thm.mp (thm.mp (thm.axk (¬' p) (¬' p)) (thm.axk (¬' p →' ¬' p →' ¬' p) (¬' (¬' (¬' p)))))
       (thm.mp
          (thm.mp
             (thm.mp
                (thm.mp
                   (thm.mp (thm.axk (¬' (¬' (¬' p))) (¬' (¬' (¬' p))))
                      (thm.mp (thm.axk (¬' (¬' (¬' p))) (¬' (¬' (¬' p)) →' ¬' (¬' (¬' p))))
                         (thm.axs (¬' (¬' (¬' p))) (¬' (¬' (¬' p)) →' ¬' (¬' (¬' p))) (¬' (¬' (¬' p))))))
                   (thm.mp
                      (thm.mp (thm.axk (¬' (¬' (¬' p))) (¬' (¬' (¬' p →' ¬' p →' ¬' p))))
                         (thm.axk
                            (¬' (¬' (¬' p)) →' ¬' (¬' (¬' p →' ¬' p →' ¬' p)) →' ¬' (¬' (¬' p)))
                            (¬' (¬' (¬' p)))))
                      (thm.axs (¬' (¬' (¬' p))) (¬' (¬' (¬' p)))
                         (¬' (¬' (¬' p →' ¬' p →' ¬' p)) →' ¬' (¬' (¬' p))))))
                (thm.mp
                   (thm.mp (thm.axn (¬' (¬' p)) (¬' (¬' p →' ¬' p →' ¬' p)))
                      (thm.axk
                         ((¬' (¬' (¬' p →' ¬' p →' ¬' p)) →' ¬' (¬' (¬' p))) →'
                            ¬' (¬' p) →' ¬' (¬' p →' ¬' p →' ¬' p))
                         (¬' (¬' (¬' p)))))
                   (thm.axs (¬' (¬' (¬' p))) (¬' (¬' (¬' p →' ¬' p →' ¬' p)) →' ¬' (¬' (¬' p)))
                      (¬' (¬' p) →' ¬' (¬' p →' ¬' p →' ¬' p)))))
             (thm.mp
                (thm.mp (thm.axn (¬' p →' ¬' p →' ¬' p) (¬' p))
                   (thm.axk
                      ((¬' (¬' p) →' ¬' (¬' p →' ¬' p →' ¬' p)) →'
                         (¬' p →' ¬' p →' ¬' p) →' ¬' p)
                      (¬' (¬' (¬' p)))))
                (thm.axs (¬' (¬' (¬' p))) (¬' (¬' p) →' ¬' (¬' p →' ¬' p →' ¬' p))
                   ((¬' p →' ¬' p →' ¬' p) →' ¬' p))))
          (thm.axs (¬' (¬' (¬' p))) (¬' p →' ¬' p →' ¬' p) (¬' p))))
    (thm.axn p (¬' (¬' p)))

#exit
@[derive decidable_eq] inductive fml
| atom (i : ℕ)
| imp (a b : fml)
| not (a : fml)

open fml

infixr ` →' `:50 := imp -- right associative

prefix `¬' `:40 := fml.not

inductive prf : fml → Type
| axk (p q) : prf (p →' q →' p)
| axs (p q r) : prf $ (p →' q →' r) →' (p →' q) →' (p →' r)
| axX (p q) : prf $ ((¬' q) →' (¬' p)) →' p →' q
| mp {p q} : prf p → prf (p →' q) → prf q

#print prf.rec

open prf

/-
-- example usage:
lemma p_of_p_of_p_of_q (p q : fml) : prf $ (p →' q) →' (p →' p) :=
begin
  apply mp (p →' q →' p) ((p →' q) →' p →' p) (axk p q),
  exact axs p q p
end
-/

def is_not : fml → Prop :=
λ f, ∃ g : fml, f = ¬' g

#print prf.rec_on
theorem Q6b (f : fml) (p : prf f) : is_not f → false :=
begin
  induction p,
  {admit},
  {admit},
  {admit},
  {
    clear p_ih_a_1,
    }


end

#print Q6b

theorem Q6b : ∀ p : fml, ¬(prf $ p →' ¬' ¬' p) :=
begin
  cases p,


end


#exit

import data.fintype

section

@[derive decidable_eq] inductive cbool
| t : cbool
| f : cbool
| neither : cbool
open cbool

instance : fintype cbool := ⟨{t,f,neither}, λ x, by cases x; simp⟩

variables (imp : cbool → cbool → cbool) (n : cbool → cbool)
  (a1 : ∀ p q, imp p (imp q p) = t)
  (a2 : ∀ p q, imp (imp (n q) (n p)) (imp p q) = t)
  (a3 : ∀ p q r, imp (imp p (imp q r)) (imp (imp p q) (imp p r)) = t)
include a1 a2 a3

set_option class.instance_max_depth 50

-- example : ∀ p, imp p (n (n p)) = t :=
-- by revert imp n; exact dec_trivial



end

open finset

instance inst1 : has_repr (bool → bool) :=
⟨λ f, "(tt ↦ " ++ repr (f tt) ++ ", ff ↦ " ++ repr (f ff) ++")"⟩

instance inst2 : has_repr (bool → bool → bool) :=
⟨λ f, "(tt ↦ " ++ repr (f tt) ++ ", ff ↦ " ++ repr (f ff)++")"⟩

#eval band

#eval (((univ : finset ((bool → bool → bool) × (bool → bool))).filter
  (λ x : (bool → bool → bool) × (bool → bool),
    (∀ p q, x.1 p (x.1 q p) = tt) ∧
    (∀ p q, x.1 (x.1 (x.2 q) (x.2 p)) (x.1 p q) = tt) ∧
    (∀ p q r, x.1 (x.1 p (x.1 q r)) (x.1 (x.1 p q) (x.1 p r)) = tt)))


#exit
import ring_theory.ideals

variables {p : Prop} {α : Type*} [comm_ring α]

instance : is_ideal {x : α | x = 0 ∨ p} :=
{ to_is_submodule :=
  ⟨or.inl rfl,
    λ x y hx hy, hx.elim (λ hx0, by rw [hx0, zero_add]; exact hy) or.inr,
    λ c x hx, hx.elim (λ hx0, by rw [hx0, smul_eq_mul, mul_zero]; exact or.inl rfl) or.inr⟩ }

def h : is_ideal {x : ℤ | x = 0 ∨ p} := by apply_instance
set_option pp.implicit true
#print axioms set_of.is_ideal
#print axioms nonzero_comm_ring.to_comm_ring

#exit
import algebra.pi_instances

variables {G₁ G₂ G₃ : Type} [group G₁] [group G₂] [group G₃]

def isom : {f : (G₁ × (G₂ × G₃)) ≃ ((G₁ × G₂) × G₃) // is_group_hom f} :=
⟨⟨λ ⟨a, ⟨b, c⟩⟩, ⟨⟨a, b⟩, c⟩, λ ⟨⟨a, b⟩, c⟩, ⟨a, b, c⟩, λ ⟨_, _, _⟩, rfl, λ ⟨⟨_, _⟩, _⟩, rfl⟩, ⟨λ ⟨_, _, _⟩ ⟨_, _, _⟩, rfl⟩⟩



#exit
import data.equiv.denumerable
open denumerable
#eval of_nat (ℤ × ℤ) 145903

#exit
import data.polynomial ring_theory.ideals
open polynomial euclidean_domain

def gaussian_integers := @quotient_ring.quotient (polynomial ℤ) _
  (span ({(X : polynomial ℤ) ^ 2 + 1} : set (polynomial ℤ)))
  (is_ideal.span ({X ^ 2 + 1} : set (polynomial ℤ)))

instance : decidable_eq gaussian_integers :=
λ x y, begin  end




#eval gcd_a (-5 : ℤ) (-11)

local notation `f` := ((X : polynomial ℚ) ^ 2 * C (53/96) - 22 * X - 141)
local notation `g` := (23 * (X : polynomial ℚ) ^ 3 -  44 * X^2 + 3 * X - 2)

#eval (5 / 4 : ℚ)
#eval gcd_a f g * C (coeff (gcd f g) 0)⁻¹
#eval gcd f g
#eval (f * (gcd_a f g * C (coeff (gcd f g) 0)⁻¹) - 1) % g




#exit
import data.nat.choose data.nat.prime
open nat

lemma prime_dvd_fact_iff : ∀ {n p : ℕ} (hp : prime p), p ∣ n.fact ↔ p ≤ n
| 0 p hp := by simp [nat.pos_iff_ne_zero.1 hp.pos, ne.symm (ne_of_lt hp.gt_one)]
| (n+1) p hp := begin
  rw [fact_succ, hp.dvd_mul, prime_dvd_fact_iff hp],
  exact ⟨λ h, h.elim (le_of_dvd (succ_pos _)) le_succ_of_le,
    λ h, (lt_or_eq_of_le h).elim (or.inr ∘ le_of_lt_succ) (λ h, by simp [h])⟩
end

example {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : prime p) : p ∣ choose p k :=
(hp.dvd_mul.1 (show p ∣ choose p k * (fact k * fact (p - k)),
  by rw [← mul_assoc, choose_mul_fact_mul_fact (le_of_lt hkp)];
    exact dvd_fact hp.pos (le_refl _))).resolve_right
      (by rw [hp.dvd_mul, prime_dvd_fact_iff hp,
          prime_dvd_fact_iff hp, not_or_distrib, not_le, not_le];
        exact ⟨hkp, nat.sub_lt_self hp.pos hk⟩)



#exit
#print eq

inductive Id {α : Type} (x : α) : α → Type
| refl : Id x

lemma T1 {α : Type} (x y : α) (i j : Id x y) : i = j :=
by cases i; cases j; refl
#print T1

#reduce T1

lemma T2 {α : Type} (x y : α) (i j : Id x y) : Id i j :=
begin cases i; cases j; constructor end

#print T2

#exit
import group_theory.quotient_group analysis.topology.topological structures

instance {α : Type*} [topological_group α] (S : set α) [normal_subgroup S] :
  topological_space (quotient_group.quotient S) := by apply_instance

#exit

import analysis.real tactic.linarith

open real filter

lemma IVT {f : ℝ → ℝ} {a b : ℝ} (hf : ∀ x, a ≤ x → x ≤ b → tendsto f (nhds x) (nhds (f x)))
  (ha : f a ≤ 0) (hb : 0 ≤ f b) (hab : a ≤ b) : ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ f x = 0 :=
let x := Sup {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b} in
have hx₁ : ∃ y, ∀ g ∈ {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b}, g ≤ y := ⟨b, λ _ h, h.2.2⟩,
have hx₂ : ∃ y, y ∈ {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b} := ⟨a, ha, le_refl _, hab⟩,
have hax : a ≤ x, from le_Sup _ hx₁ ⟨ha, le_refl _, hab⟩,
have hxb : x ≤ b, from (Sup_le _ hx₂ hx₁).2 (λ _ h, h.2.2),
⟨x, hax, hxb,
  eq_of_forall_dist_le $ λ ε ε0,
    let ⟨δ, hδ0, hδ⟩ := tendsto_nhds_of_metric.1 (hf _ hax hxb) ε ε0 in
    (le_total 0 (f x)).elim
      (λ h, le_of_not_gt $ λ hfε, begin
        rw [dist_0_eq_abs, abs_of_nonneg h] at hfε,
        refine mt (Sup_le {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b} hx₂ hx₁).2
          (not_le_of_gt (sub_lt_self x (half_pos hδ0)))
          (λ g hg, le_of_not_gt
            (λ hgδ, not_lt_of_ge hg.1
              (lt_trans (sub_pos_of_lt hfε) (sub_lt_of_sub_lt
                (lt_of_le_of_lt (le_abs_self _) _))))),
        rw abs_sub,
        exact hδ (abs_sub_lt_iff.2 ⟨lt_of_le_of_lt (sub_nonpos.2 (le_Sup _ hx₁ hg)) hδ0,
          by simp only [x] at *; linarith⟩)
        end)
      (λ h, le_of_not_gt $ λ hfε, begin
        rw [dist_0_eq_abs, abs_of_nonpos h] at hfε,
        exact mt (le_Sup {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b})
          (λ h : ∀ k, k ∈ {x | f x ≤ 0 ∧ a ≤ x ∧ x ≤ b} → k ≤ x,
            not_le_of_gt ((lt_add_iff_pos_left x).2 (half_pos hδ0))
              (h _ ⟨le_trans (le_sub_iff_add_le.2 (le_trans (le_abs_self _)
                    (le_of_lt (hδ $ by rw [dist_eq, add_sub_cancel, abs_of_nonneg (le_of_lt (half_pos hδ0))];
                      exact half_lt_self hδ0))))
                  (le_of_lt (sub_neg_of_lt hfε)),
                le_trans hax (le_of_lt ((lt_add_iff_pos_left _).2 (half_pos hδ0))),
                le_of_not_gt (λ hδy, not_lt_of_ge hb (lt_of_le_of_lt (show f b ≤ f b - f x - ε, by linarith)
                  (sub_neg_of_lt (lt_of_le_of_lt (le_abs_self _)
                    (@hδ b (abs_sub_lt_iff.2 ⟨by simp only [x] at *; linarith,
                      by linarith⟩))))))⟩))
          hx₁
        end)⟩

#print IVT

#exit
import tactic.norm_num tactic.ring tactic.linarith

lemma h (x y z : ℤ) (h₁ : 0 ≤ x) (h₂ : y + x ≤ z) : y ≤ z :=
by linarith

#print h

open nat

lemma prime_seven : prime 7 := by norm_num

#print prime_seven

lemma ring_thing (x y z : ℤ) : x ^ 2 - x * (y - z) - z * x = x * (x - y) := by ring

#print ring_thing

example (x : ℤ) (h : ∃ y, x = y ∧ x ^ 2 = 2)  :
open nat zmodp

lemma p7 : prime 7 := by norm_num

theorem foo (x y : zmodp 7 p7) (h : x ≠ y) : (x - y) ^ 6 = 1 :=
fermat_little p7 (sub_ne_zero.2 h)

#exit
import data.polynomial
import linear_algebra.multivariate_polynomial
import ring_theory.associated

universe u

namespace algebraic_closure

variables (k : Type u) [field k] [decidable_eq k]

def irred : set (polynomial k) :=
{ p | irreducible p }

def big_ring : Type u :=
mv_polynomial (irred k) k

instance : comm_ring (big_ring k) :=
mv_polynomial.comm_ring

instance : module (big_ring k) (big_ring k) := by apply_instance

instance : decidable_eq (big_ring k) := by apply_instance

instance foo : decidable_eq (irred k) := by apply_instance

set_option profiler true
def big_ideal : set (big_ring k) :=
span (⋃ p : irred k, { polynomial.eval₂ (@mv_polynomial.C k (irred k) _ _ _)
  (@mv_polynomial.X k (irred k) _ _ _ p) p.1 })

#exit
import data.nat.basic

#print dlist

@[simp] lemma nat.strong_rec_on_beta {p : nat → Sort*} : ∀ (n : nat) (h : ∀ n, (∀ m, m < n → p m) → p n),
  (nat.strong_rec_on n h : p n) = h n (λ m H, nat.strong_rec_on m h)
| 0 h := begin simp [nat.strong_rec_on, or.by_cases], congr, funext,
  exact (nat.not_lt_zero _ h₁).elim, intros, end

#exit
meta def foo (n : ℕ) : option ℕ :=
do let m : ℕ :=
  match n with
  | 0     := 1
  | (n+1) := by exact _match n + _match n
  end,
return m
#print foo
#eval foo 4 -- some 16



-- begin
--   let m : ℕ :=
--   match n with
--   | 0     := 1
--   | (n+1) := _match n + _match n
--   end,
--   have h : m = 2 ^ n, by induction n;
--     simp [nat.mul_succ, nat.succ_mul, *, m, _example._match_1, nat.pow_succ] at *,

-- end


import set_theory.cardinal
#print list.zip_with
open cardinal

example (α : Type*) (S T : set α)
  (HS : set.finite S) (HT : set.finite T)
  (H : finset.card (set.finite.to_finset HS) ≤ finset.card (set.finite.to_finset HT)) :
  cardinal.mk S ≤ cardinal.mk T :=
begin
  haveI := classical.choice HS,
  haveI := classical.choice HT,
  rwa [fintype_card S, fintype_card T, nat_cast_le,
    set.card_fintype_of_finset' (set.finite.to_finset HS),
    set.card_fintype_of_finset' (set.finite.to_finset HT)];
  simp
end



example (f g : ℕ → ℕ) : (∀ x : ℕ, f x = g x) → f ≈ g := id
#print funext

#exit
import data.nat.modeq tactic.find

example (p : ℕ) (nine : 2 ∣ p / 2) (thing11 : 3 + 4 * (p / 4) = p) : false :=
begin
  rw [nat.dvd_iff_mod_eq_zero, ← nat.mod_mul_right_div_self,
    ← thing11, show 2 * 2 = 4, from rfl, nat.add_mul_mod_self_left] at nine,
  contradiction


end
#exit
import data.list.sort data.string

meta def list_constant (e : expr) : rbtree name :=
e.fold (mk_rbtree name) $ λ e _ cs,
let n := e.const_name in
if e.is_constant
then cs.insert n
else cs

open declaration tactic

meta def const_in_def (n : name) : tactic (list name) :=
do d ← get_decl n,
match d with
| thm _ _ t v      := return (list_constant v.get ∪ list_constant t)
| defn _ _ t v _ _ := return (list_constant v ∪ list_constant t)
| cnst _ _ t _     := return (list_constant t)
| ax _ _ t         := return (list_constant t)
end

meta def const_in_def_trans_aux : list name × list (name × list name) →
  tactic (list name × list (name × list name))
| ([], l₂) := pure ([], l₂)
| (l₁, l₂) :=
do l' ← l₁.mmap (λ n, do l ← const_in_def n, return (n, l)),
let l2 := l' ++ l₂,
const_in_def_trans_aux ((l'.map prod.snd).join.erase_dup.diff (l2.map prod.fst), l2)

meta def const_in_def_trans (n : name) : tactic unit :=
do l ← const_in_def_trans_aux ([n], []),
trace l.2.length,
trace (list.insertion_sort (≤) (l.2.map to_string)),
return ()

meta def list_all_consts : tactic (list name) :=
do e ← get_env,
let l : list name := environment.fold e []
  (λ d l, match d with
    | thm n _ _ _ := n :: l
    | defn n _ _ _ _ _ := n :: l
    | cnst n _ _ _ := n :: l
    | ax n _ _ := n :: l end),
trace l,
trace l.length,
return l

meta def trans_def_all_aux : list name → rbmap name (rbtree name)
  → rbmap name (rbtree name) → option (rbmap name (rbtree name))
| []      m₁ m₂ := pure m₂
| (n::l₁) m₁ m₂ :=
do l₁ ← m₁.find n,
l₂ ← l₁.mmap m₁.find,
let l₃ := l₂.join,
if l₃ = l₁ then trans_def_all_aux l₁ (m₁.erase n)
else sorry



meta def trans_def_list (l : list name) : tactic unit :=
do
map ← l.mmap (λ n, do l' ← const_in_def n, return (n, l)),
m ← trans_def_all_aux [`prod.swap] (pure (rbmap.from_list map)),
let result := m.to_list,
trace (result.map (λ n, (n.1, n.2.length))),
return ()

meta def trans_def_list_all : tactic unit :=
do l ← list_all_consts,
trans_def_list l,
return ()

#eval const_in_def_trans `prod.swap

-- #eval trans_def_list_all


#exit

#print list.union
meta def const_in_def_trans_aux : Π (n : name), tactic (list name)
| n := do d ← get_decl n,
match d with
| thm _ _ t v := do
  let v := v.get,
  let l := list_constant v,
--  do m ← l.mmap const_in_def_trans_aux,
  return (l).erase_dup
| defn _ _ t v _ _ := do
  let l := list_constant v,
  do m ← l.mmap const_in_def_trans_aux,
  return (l).erase_dup
| d := pure []
end

meta def const_in_def_depth_aux : ℕ → name → list name → tactic (list name)
| 0     n p := pure []
| (m+1) n p :=
do d ← get_decl n,
match d with
| thm _ _ t v := do
  let v := v.get,
  let l := (list_constant v).diff p,
  let q := p ++ l,
  l' ← l.mmap (λ n, const_in_def_depth_aux m n q),
  return (l ++ l'.bind id).erase_dup
| defn _ _ t v _ _ := do
  let l := (list_constant v).diff p,
  let q := p ++ l,
  l' ← l.mmap (λ n, const_in_def_depth_aux m n q),
  return (l ++ l'.bind id).erase_dup
| d := pure []
end



meta def const_in_def_depth_aux' : ℕ → Π n : name, tactic (list name)
| 0     n := pure []
| (m+1) n :=
do d ← get_decl n,
match d with
| thm _ _ t v := do
  let v := v.get,
  let l := list_constant v,
  l' ← l.mmap (const_in_def_depth_aux' m),
  return (l'.bind id ++ l).erase_dup
| defn _ _ t v _ _ := do
  let l := list_constant v,
  l' ← l.mmap (const_in_def_depth_aux' m),
  return (l'.bind id ++ l).erase_dup
| d := pure []
end

meta def const_in_def_depth (m : ℕ) (n : name) : tactic unit :=
do l ← const_in_def_depth_aux m n [],
  trace l.length,
  trace l,
  return ()

meta def const_in_def_depth' (m : ℕ) (n : name) : tactic unit :=
do l ← const_in_def_depth_aux' m n,
  trace l.length,
  trace l,
  return ()

meta def const_in_def_trans (n : name) : tactic unit :=
do l ← const_in_def_trans_aux n,
  trace l.length,
  trace l,
  return ()

set_option profiler true

-- #eval const_in_def_depth' 3 `polynomial.euclidean_domain

-- #eval const_in_def_depth 5 `polynomial.euclidean_domain



-- meta def const_in_def₂  (n : name) : tactic (list name) :=
-- do l ← const_in_def n,
-- m ← l.mmap const_in_def,
-- trace m,
-- return l
#print simp_config

#exit
 data.zmod.basic data.polynomial tactic.norm_num data.rat.basic

instance h {p : ℕ} (hp : nat.prime p) : has_repr (zmodp p hp) := fin.has_repr _

open polynomial
#eval (11 * X ^ 20 + 7 * X ^ 9 + 12 * X + 11 :
  polynomial ℚ) / (22 * X ^ 2 - 1)


#exit
import algebra.big_operators

open finset

lemma prod_involution (s : finset β) {f : β → α} :
  ∀ (g : Π a ∈ s, β)
  (h₁ : ∀ a ha, f a * f (g a ha) = 1)
  (h₂ : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
  (h₃ : ∀ a ha, g a ha ∈ s)
  (h₄ : ∀ a ha, g (g a ha) (h₃ a ha) = a),
  s.prod f = 1 :=
by haveI := classical.dec_eq β;
haveI := classical.dec_eq α; exact
finset.strong_induction_on s
  (λ s ih g h₁ h₂ h₃ h₄,
    if hs : s = ∅ then hs.symm ▸ rfl
    else let ⟨x, hx⟩ := exists_mem_of_ne_empty hs in
      have hmem : ∀ y ∈ (s.erase x).erase (g x hx), y ∈ s,
        from λ y hy, (mem_of_mem_erase (mem_of_mem_erase hy)),
      have g_inj : ∀ {x hx y hy}, g x hx = g y hy → x = y,
        from λ x hx y hy h, by rw [← h₄ x hx, ← h₄ y hy]; simp [h],
      have ih': (erase (erase s x) (g x hx)).prod f = (1 : α) :=
        ih ((s.erase x).erase (g x hx))
          ⟨subset.trans (erase_subset _ _) (erase_subset _ _),
            λ h, not_mem_erase (g x hx) (s.erase x) (h (h₃ x hx))⟩
          (λ y hy, g y (hmem y hy))
          (λ y hy, h₁ y (hmem y hy))
          (λ y hy, h₂ y (hmem y hy))
          (λ y hy, mem_erase.2 ⟨λ (h : g y _ = g x hx), by simpa [g_inj h] using hy,
            mem_erase.2 ⟨λ (h : g y _ = x),
              have y = g x hx, from h₄ y (hmem y hy) ▸ by simp [h],
              by simpa [this] using hy, h₃ y (hmem y hy)⟩⟩)
          (λ y hy, h₄ y (hmem y hy)),
      if hx1 : f x = 1
      then ih' ▸ eq.symm (prod_subset hmem
        (λ y hy hy₁,
          have y = x ∨ y = g x hx, by simp [hy] at hy₁; tauto,
          this.elim (λ h, h.symm ▸ hx1)
            (λ h, h₁ x hx ▸ h ▸ hx1.symm ▸ (one_mul _).symm)))
      else by rw [← insert_erase hx, prod_insert (not_mem_erase _ _),
        ← insert_erase (mem_erase.2 ⟨h₂ x hx hx1, h₃ x hx⟩),
        prod_insert (not_mem_erase _ _), ih', mul_one, h₁ x hx])

lemma prod_univ_units_finite_field {α : Type*} [fintype α] [field α] [decidable_eq α] : univ.prod (λ x, x) = (-1 : units α) :=
have h₁ : ∀ x : units α, x ∈ (univ.erase (-1 : units α)).erase 1 → x⁻¹ ∈ (univ.erase (-1 : units α)).erase 1,
  from λ x, by rw [mem_erase, mem_erase, mem_erase, mem_erase, ne.def, ne.def, ne.def,
    ne.def, inv_eq_iff_inv_eq, one_inv, inv_eq_iff_inv_eq]; simp; cc,
have h₂ : ∀ x : units α, x ∈ (univ.erase (-1 : units α)).erase 1 → x⁻¹ ≠ x,
  from λ x, by  rw [ne.def, units.inv_eq_self_iff]; finish,
calc univ.prod (λ x, x) = (insert (1 : units α) (insert (-1 : units α) ((univ.erase (-1 : units α)).erase 1))).prod (λ x, x) :
  by congr; simp [finset.ext]; tauto
... = -((univ.erase (-1 : units α)).erase 1).prod (λ x, x) :
  if h : (1 : units α) = -1
  then by rw [insert_eq_of_mem, prod_insert]; simp *; cc
  else by rw [prod_insert, prod_insert]; simp *
... = -1 : by rw [prod_finset_distinct_inv h₁ h₂]
#exit
import data.equiv.basic
variables {α : Type*} {β : Type*} [preorder α] [preorder β]

example (f : α ≃ β) (hf : ∀ a b, a ≤ b → f a ≤ f b)
  (hf' : ∀ a b, a ≤ b → f.symm a ≤ f.symm b) : ∀ a b, a < b ↔ f a < f b :=
have ∀ a b, a ≤ b ↔ f a ≤ f b, from λ a b,
⟨hf a b, λ h, by rw [← equiv.inverse_apply_apply f a, ← equiv.inverse_apply_apply f b];
  exact hf' (f a) (f b) h⟩,
λ a b, by simp [lt_iff_le_not_le, this]

#exit
import analysis.real




def g : topological_space ℝ := by apply_instance


theorem nonethm {t} : (none <|> none)=@none t := rfl

#exit
import data.nat.basic data.fintype.basic algebra.group_power

instance nat.decidable_bexists_lt (n : ℕ) (P : Π k < n, Prop)
  [∀ k h, decidable (P k h)] : decidable (∃ k h, P k h) :=
decidable_of_iff (¬ ∀ k h, ¬ P k h) $ by simp [classical.not_forall]

instance nat.decidable_bexists_le (n : ℕ) (P : Π k ≤ n, Prop)
  [∀ k h, decidable (P k h)] : decidable (∃ k h, P k h) :=
decidable_of_iff (∃ (k) (h : k < n.succ), P k (nat.le_of_lt_succ h))
  ⟨λ ⟨k, hk, h⟩, ⟨k, nat.le_of_lt_succ hk, h⟩,
  λ ⟨k, hk, h⟩, ⟨k, nat.lt_succ_of_le hk, h⟩⟩

instance decidable_mul_self_nat (n : ℕ) : decidable (∃ k, k * k = n) :=
decidable_of_iff (∃ k ≤ n, k * k = n)
⟨λ ⟨k, h1, h2⟩, ⟨k, h2⟩, λ ⟨k, h1⟩, ⟨k, h1 ▸ nat.le_mul_self k, h1⟩⟩

instance decidable_sqr_nat (n : ℕ) : decidable (∃ k, k^2 = n) :=
decidable_of_iff (∃ k, k * k = n)
⟨λ ⟨k, h⟩, ⟨k, by rwa [nat.pow_two]⟩, λ ⟨k, h⟩, ⟨k, by rwa [nat.pow_two] at h⟩⟩

instance decidable_mul_self_int : Π (n : ℤ), decidable (∃ k, k * k = n)
| (int.of_nat n) := decidable_of_iff (∃ k, k * k = n)
    ⟨λ ⟨k, hk⟩, ⟨k, by rw [← int.coe_nat_mul, hk]; refl⟩,
    λ ⟨k, hk⟩, ⟨int.nat_abs k, by rw [← int.nat_abs_mul, hk]; refl⟩⟩
| -[1+ n] := is_false $ λ ⟨k, h1⟩, not_lt_of_ge (mul_self_nonneg k) $
    h1.symm ▸ int.neg_succ_of_nat_lt_zero n

instance decidable_sqr_int (n : ℤ) : decidable (∃ k, k^2 = n) :=
decidable_of_iff (∃ k, k * k = n)
⟨λ ⟨k, h⟩, ⟨k, by rwa [pow_two]⟩, λ ⟨k, h⟩, ⟨k, by rwa [pow_two] at h⟩⟩

theorem what_i_need: ¬ (∃ n : ℤ , n ^ 2 = 2 ) := dec_trivial

#exit
import data.polynomial data.rat.basic tactic.ring
open polynomial nat

def gcd' : ℕ → ℕ → ℕ
| 0        y := y
| (succ x) y := have y % succ x < succ x, from classical.choice ⟨mod_lt _ $ succ_pos _⟩,
                gcd (y % succ x) (succ x)

set_option pp.proofs true
#reduce (classical.choice (show nonempty true, from ⟨trivial⟩))

#print list.foldr
#print char
#eval (X ^ 17 + 2 * X + 1 : polynomial ℚ) / (17 * X ^ 9 + - 21/17 * X ^ 14 - 5 * X ^ 4 * 5)

example : (-17/21 * X ^ 3 : polynomial ℚ) = sorry

#eval ((1/17 * X ^ 8 + -25/289 * X ^ 3 : polynomial ℚ) =
  (C (1/17) * X ^ 8 + C (-25/289) * X ^ 3 : polynomial ℚ) : bool)

example : (1/17 * X ^ 8 + -25/289 * X ^ 3 : polynomial ℚ) =
  (C (1/17) * X ^ 8 + C -25 X ^ 3 : polynomial ℚ) := begin
  ℤ

end

example : (X ^ 2 + 2 * X + 1 : polynomial ℤ) %ₘ (X + 1) = 0 :=
(dvd_iff_mod_by_monic_eq_zero dec_trivial).2 ⟨X + 1, by ring⟩


#exit
import data.zmod

instance h (m : ℤ) : decidable (∃ n : ℤ, n ^ 2 = m) :=
decidable_of_iff (0 ≤ m ∧ m.nat_abs.sqrt ^ 2 = m.nat_abs)
⟨λ h, ⟨nat.sqrt m.nat_abs, by rw [← int.coe_nat_pow, h.2, int.nat_abs_of_nonneg h.1]⟩,
 λ ⟨s, hs⟩, ⟨hs ▸ (pow_two_nonneg _), by rw [← hs, pow_two, int.nat_abs_mul, nat.sqrt_eq, nat.pow_two]⟩⟩

#eval (∄ n : ℤ, n ^ 2 = 2 : bool)
#print nat.gcd._main._pack
example : nat.gcd 4 5 = 1 := rfl

lemma two_not_square : ∄ n : ℤ, n ^ 2 = 2 := dec_trivial

example : ∄ n : ℤ, n ^ 2 = 2 :=
λ ⟨n, hn⟩, have h : ∀ n : zmod 3, n ^ 2 ≠ (2 : ℤ), from dec_trivial,
by have := h n; rw ← hn at this; simpa


example (d : ℤ) : d * d ≡ 0 [ZMOD 8] ∨ d * d ≡ 1 [ZMOD 8] ∨ d * d ≡ 4 [ZMOD 8] :=
have ∀ d : zmod 8, d * d = (0 : ℤ) ∨ d * d = (1 : ℤ) ∨ d * d = (4 : ℤ), from dec_trivial,
by have := this d;
  rwa [← int.cast_mul, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int, zmod.eq_iff_modeq_int] at this

example (a b : ℤ) (h : a ≡ b [ZMOD 8]) : a ^ 2 ≡ b ^ 2 [ZMOD 8] :=
by rw [pow_two, pow_two]; exact int.modeq.modeq_mul h h

example : ∀ a b : zmod 8, a = b → a ^ 2 = b ^ 2 := dec_trivial



open finset
def thing : ℕ → Type := λ n : ℕ,
well_founded.fix nat.lt_wf (λ (x) (ih : Π (y : ℕ), nat.lt y x → Type),
  Π (m : fin x), ih m.1 m.2) n

lemma thing_eq : thing =
  (λ n, (Π m : fin n, thing m.1)) :=
begin
  funext,
  rw [thing],
  dsimp,
  rw [well_founded.fix_eq]
end

instance : ∀ n : ℕ, fintype (thing n)
| 0 := ⟨finset.singleton (begin rw thing_eq, exact λ ⟨m, hm⟩, (nat.not_lt_zero _ hm).elim end),
  λ x, mem_singleton.2 (funext $ λ ⟨m, hm⟩, (nat.not_lt_zero _ hm).elim)⟩
| (n+1) := begin
  haveI : ∀ m : fin (n + 1), fintype (thing m.1) :=
    λ m, have m.1 < n + 1, from m.2, thing.fintype m.1,
  rw thing_eq,
  apply_instance
end

#eval fintype.card (thing 4)

example (n : nat) : thing n = sorry :=
begin
  rw thing_eq, rw thing_eq, rw thing_eq, rw thing_eq, rw thing_eq, rw thing_eq,
  dsimp,
end

import data.int.basic

#print int.nat_abs_ne

#exit
class principal_ideal_domain (α : Type*) extends comm_ring α :=
(principal : ∀ (S : set α) [is_ideal S], ∃ a, S = {x | a ∣ x})

lemma prime_factors (n : ℕ) : ∃ l : list ℕ, (∀ p, p ∈ l → nat.prime p) ∧ l.prod = n :=
begin


end

#exit
class has_group_notation (G : Type) extends has_mul G, has_one G, has_inv G

class group' (G : Type) extends has_group_notation G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)
-- Lean 3.4.1 also uses mul_one : ∀ (a : G), a * 1 = a , but we'll see we can deduce it!
-- Note : this doesn't matter at all :-)

variables {G : Type} [group' G]
namespace group'

lemma mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c :=
λ (a b c : G) (Habac : a * b = a * c), -- got to deduce b = c.
calc b = 1 * b : by rw one_mul
... = (a⁻¹ * a) * b : by rw mul_left_inv
... = a⁻¹ * (a * b) : by rw mul_assoc
... = a⁻¹ * (a * c) : by rw Habac
... = (a⁻¹ * a) * c : by rw mul_assoc
... = 1 * c : by rw mul_left_inv
... = c : by rw one_mul

-- now the main theorem

theorem mul_one : ∀ (a : G), a * 1 = a :=
begin
intro a, -- goal is a * 1 = a
apply mul_left_cancel a⁻¹, -- goal now a⁻¹ * (a * 1) = a⁻¹ * a
exact calc a⁻¹ * (a * 1) = (a⁻¹ * a) * 1 : by rw mul_assoc
... = 1 * 1 : by rw mul_left_inv
... = 1 : by rw one_mul
... = a⁻¹ * a : by rw ← mul_left_inv
end
#print mul_one
#exit
import data.nat.basic
#print nat.nat.find_greatest
def nat.find_greatest (P : ℕ → Prop) [decidable_pred P] : ℕ → ℕ
| 0     := 0
| (n+1) := if h : P (n + 1) then n + 1 else nat.find_greatest n

lemma n (α : Type) (n : ℕ) (Hn : cardinal.mk α = n) :
  ∃ l : list α, l.nodup ∧ l.length = n :=
have fintype α, from classical.choice (cardinal.lt_omega_iff_fintype.1
  (Hn.symm ▸ cardinal.nat_lt_omega _)),
let ⟨l, hl⟩ := quotient.exists_rep (@finset.univ α this).1 in
⟨l, show multiset.nodup ⟦l⟧, from hl.symm ▸ (@finset.univ α this).2,
  begin end⟩

lemma three (α : Type) (Hthree : cardinal.mk α = 3) :
  ∃ a b c : α, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ∀ d : α, d = a ∨ d = b ∨ d = c :=
by simp
ₘ
example (s : finset ℕ) : Type := (↑s : set ℕ)

def thing (n : ℕ) := n.factors.erase_dup.length

#eval thing 217094830932814709123840973089487098175


example : f(g*h) = f(g) * f(h) := sorry

def A : set ℝ := {x | x^2 < 3}
def B : set ℝ := {x | x^2 < 3 ∧ ∃ y : ℤ, x = y}

lemma foo : (1 / 2 : ℝ) ∈ A ∩ B :=
begin
split,
rw [A, set.mem_set_of_eq],

{norm_num},


end

example : (1 / 2 : ℝ)^2 < 3 := by norm_num


import data.zmod

lemma gcd_one_of_unit {n : ℕ+} (u : units (zmod n)) :
nat.gcd (u.val.val) n = 1 :=
begin
let abar := u.val, let bbar := u.inv, -- in zmod n
let a := abar.val, let b := bbar.val, -- in ℕ
have H : (a b) % n = 1 % n,
show (abar.val bbar.val) % n = 1 % n,
rw ←mul_val,
rw u.val_inv,
refl,
let d := nat.gcd a n,
show d = 1,
rw ←nat.dvd_one,
rw ←dvd_mod_iff (gcd_dvd_right a n),
rw ←H,
rw dvd_mod_iff (gcd_dvd_right a n),
apply dvd_mul_of_dvd_left,
exact gcd_dvd_left a n
end

lemma hintq3a : ∀ (a b c : zmod 4), 0 = a^2 + b^2 + c^2 → (2 ∣ a ∧ 2 ∣ b ∧ 2 ∣ c) := dec_trivial

lemma zmod.cast_nat_dvd {n : ℕ+} {a b : ℕ} (h : a ∣ n) : (a : zmod n) ∣ b ↔ a ∣ b := sorry


#exit
import data.set.basic tactic.interactive

variables {α : Type*} [ring α] (S T : set α)

instance : has_mul (set α) := ⟨λ S T, {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t}⟩
lemma mul_def : S * T =  {x | ∃ s ∈ S, ∃ t ∈ T, x = s * t} := rfl

instance : has_add (set α) :=  ⟨λ S T, {x | ∃ s ∈ S, ∃ t ∈ T, x = s + t}⟩
lemma add_def : S + T =  {x | ∃ s ∈ S, ∃ t ∈ T, x = s + t} := rfl

instance : has_one (set α) := ⟨{1}⟩

instance : has_zero (set α) := ⟨{0}⟩

instance {α : Type*} [ring α] : semiring (set α) :=
{ one_mul := λ a, set.ext $ by simp,
  mul_one := λ a, set.ext $ by simp,
  add_assoc := λ s t u, set.ext $ λ x, ⟨λ h,begin rcases? h,  end, sorry⟩,



  ..set.has_mul,
  ..set.has_add,
  ..set.has_one,
  ..set.has_zero }


#exit
import data.fintype

example : ∀ (f : fin 2 → fin 2 → fin 2),
  (∀ x y z, f (f x y) z = f x (f y z)) → (∀ x, f x 0 = x) →
  (∀ x, ∃ y, f x y = 0) → (∀ x y, f x y = f y x) := dec_trivial


#exit
import data.vector2

lemma vector.ext {α : Type*} {n : ℕ} : ∀ {v w : vector α n}
  (h : ∀ m : fin n, vector.nth v m = vector.nth w m), v = w :=
λ ⟨v, hv⟩ ⟨w, hw⟩ h, subtype.eq (list.ext_le (by rw [hv, hw])
(λ m hm hn, h ⟨m, hv ▸ hm⟩))

lemma vector.nth_of_fn {α : Type*} {n : ℕ} : ∀ (f : fin n → α),
  vector.nth (vector.of_fn f) = f :=

#print opt_param
inductive nested : Type
| nest : list nested → nested
#print has_inv.inv
open nested
#print nested.rec

#print prefix nested

#print vector.of_fn

def nested.rec_on (C : nested → Sort*) (x : nested)  (h0 : C (nest [])) :
  Π (h : Π (l : list nested), (Π a ∈ l, C a) → C (nest l)), C x :=
nested.cases_on _ x (
begin
  assume l,
  induction l with a l ih,
  { exact λ _, h0 },
  { assume h,
    refine h _ (λ b h, _),
     }
end

)

instance : has_well_founded nested :=
⟨λ a b, nested.rec (λ _, Prop) (λ l, a ∈ l) b,
⟨λ a, acc.intro _ (λ b, nested.cases_on _ a (begin
  assume l hb,
  simp at hb,

end))⟩⟩

def nested_dec_eq : ∀ a b : nested, decidable (a = b)
| (nest []) (nest []) := is_true rfl
| (nest []) (nest (a :: l)) := is_false (mt nest.inj (λ h, list.no_confusion h))
| (nest (a :: l)) (nest []) := is_false (mt nest.inj (λ h, list.no_confusion h))
| (nest (a :: l)) (nest (b :: m)) :=

end

#exit
import data.equiv.basic data.fintype
universes u v w

set_option trace.simplify.rewrite true
lemma thing {α : Type*} (p q : Prop) : (∃ hp : p, q) ↔ p ∧ q :=
begin
  simp,

end
#print exists_prop

#exit
#print equiv.coe_fn_mk
#print has_coe_to_fun
theorem coe_fn_mk {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l : function.left_inverse g f)
(r : function.right_inverse g f) : (equiv.mk f g l r : has_coe_to_fun.F (equiv.mk f g l r)) = f := rfl

example {α : Sort*} {β : Sort*} (f : α ≃ β) (a : ℕ) : (equiv.mk (λ a, ite (a = 5) (4 : ℕ) 5)
  sorry sorry sorry : ℕ → ℕ) = sorry :=
begin
  cases f, simp,
  simp only [coe_fn_mk],

end

#exit
import data.real.basic

lemma silly_function : ∃ f : ℝ → ℝ, ∀ x y a : ℝ, x < y → ∃ z : ℝ, x < z ∧ z < y ∧ f z = a := sorry

#print well_founded.fix
#exit
import logic.function

example (x y : ℕ) (h : x ≠ y) (f : ℕ → ℕ) (h₂ : function.injective f) :
  f x ≠ f y := mt (@h₂ x y) h

lemma em_of_iff_assoc : (∀ p q r : Prop, ((p ↔ q) ↔ r) ↔ (p ↔ (q ↔ r))) → ∀ p, p ∨ ¬p :=
λ h p, ((h (p ∨ ¬p) false false).1
⟨λ h, h.1 (or.inr (λ hp, h.1 (or.inl hp))), λ h, h.elim⟩).2 iff.rfl

#print axioms em_of_iff_assoc

#exit
import data.fintype.basic algebra.big_operators linear_algebra.linear_map_module
#print finset.smul

instance {α : Type*} [monoid α] [fintype α] : fintype (units α) :=
fintype.of_equiv {a : α // ∃ }

#exit
import data.nat.prime
import data.nat.modeq
import data.int.modeq
import algebra.group_power

namespace nat

definition quadratic_res (a n: ℕ) := ∃ x: ℕ, a ≡ x^2 [MOD n]

local attribute [instance] classical.prop_decidable

noncomputable definition legendre_sym (a: ℕ) (p:ℕ) : ℤ :=
if quadratic_res a p ∧ ¬ p ∣ a then 1 else
if ¬ quadratic_res a p then -1
else 0

theorem law_of_quadratic_reciprocity (p q : ℕ)(H1: prime p ∧ ¬ p=2)(H2: prime q ∧ ¬ q=2) :
(legendre_sym p q)*(legendre_sym q p) =(-1)^(((p-1)/2)*((q-1)/2)) := sorry

theorem euler_criterion (p : ℕ) (a: ℕ) (hp : prime p ∧ ¬ p=2) (ha : ¬ p ∣ a) :
  a^((p - 1) / 2) ≡ legendre_sym a p [MOD p] := sorry

#exit

def phi (n : nat) := ((finset.range n).filter (nat.coprime n)).card

local notation φ: = phi

lemma phi_n (n : ℕ) : phi n = fintype.card (units (Zmod n)) := sorry


lemma phi_p (p : ℕ) (hp: nat.prime p) : phi p = p-1 :=

calc phi p = p-1


#exit
import data.nat.modeq data.nat.prime data.finset data.complex.basic

#print mul_le_mul_left

definition quadratic_res (a n : ℕ) : Prop := ∃ x : ℕ, a ≡ x^2 [MOD n]

instance : decidable_rel quadratic_res :=
λ a n, if hn : n = 0 then decidable_of_iff (∃ x ∈ finset.range a, a = x^2)
⟨λ ⟨x, _, hx⟩, ⟨x, by rw hx⟩, λ ⟨x, hx⟩, ⟨x, finset.mem_range.2 begin end, begin end⟩⟩
else decidable_of_iff (∃ x ∈ finset.range n, a ≡ x^2 [MOD n])
⟨λ ⟨x, _, hx⟩, ⟨x, hx⟩, λ ⟨x, hx⟩, ⟨x % n, finset.mem_range.2 (begin end), sorry⟩ ⟩


-- definition legendre_sym (a : ℤ) (p : ℕ) :=
-- if quadratic_res a p ∧ ¬ p ∣ a then 1 else
-- if ¬ quadratic_res a p then -1
-- else 0

#exit
import algebra.group_power data.finset data.nat.gcd data.nat.prime

def phi (n : nat) := ((finset.range n).filter n.coprime).card

def phi2 (n : nat) := (n.factors.map nat.pred).prod

#eval phi 1000
#eval phi2 1000

def thing (m n : ℤ) (h : n * n < n * m) : n ^ 2 < n * m := (pow_two n).symm ▸ h

example : 2 + 3 = 5 := add_comm 0 5 ▸ rfl

lemma two_add_three2 : 2 + 3 = 5 := rfl
#exit
import data.int.basic

example (a b : ℤ) : (-3 : ℤ).nat_abs / (-5 : ℤ).nat_abs
  ≠ ((-3 : ℤ) / (- 5 : ℤ)).nat_abs :=
dec_trivial

#print tactic.interactive.induction

set_option trace.simplify.rewrite true
lemma h (α β γ : Type) (f : α → β) (g : β → α) (H : ∀ b : β, f (g b) = b)
  (j : γ → option β) (x : γ) :
  (do y ← (j x), return (f (g y))) = j x :=
by simp [H]

#print h

#exit
import analysis.real

theorem infinite_cover {a b : ℝ} {c : set (set ℝ)} (n : ℕ) :
∃ k : ℕ, 1 ≤ k ≤ n ∧ ∀ c' ⊆ c, {r : ℝ | a+(k-1)*(a+b)/n ≤ r ∧
r ≤ a+k*(a+b)/n} ⊆ ⋃₀ c' → ¬ set.finite c' := sorry

example : ∃! x, x = 2 := ⟨2, rfl, λ y, id⟩
#print exists_unique
#exit

#print array



def f : ℕ → ℕ → ℕ → ℕ → Prop

notation a `≡` b := f a b

set_option pp.implicit true
lemma h : ¬ (2 ∣ 5) := dec_trivial
#print nat.decidable_dvd

example : ¬ (2 | 5) := dec_trivial
open vector_space
variables {α β γ : Type}
  [field α] [vector_space α β] [vector_space α γ]

inductive T : Type
| mk : (ℕ → T) → T

#print T

#exit
import tactic.finish

variables (p q : Prop) (hp : p) (hq : q)

lemma easy : p ↔ p := iff.rfl

theorem not_a_constructivist : (¬(p ∨ q)) ↔ ((¬ p) ∧ (¬ q)) :=
  by finish

#print not_a_constructivist
#exit
import logic.function
open function

def f : (thunk ℕ) → ℕ  := λ _, 0

def g : ℕ → ℕ := λ _, 0

#print thunk

#eval f ((99 : ℕ) ^ 99 ^ 99)

#eval g (99 ^ 99 ^ 99 ^ 99 ^ 99)

#check Σ α : Type, set α

structure g :=
(α : Type)
(f : α → bool)

#print tactic.exact

def gafd (p q : Prop) [decidable p] [decidable q] :
  decidable (p → q) := by apply_instance
#print forall_prop_decidable


def h {α : Sort*} (f : α → α → ℕ) : ¬ surjective f :=
λ h, let ⟨a, ha⟩ := h (λ a, nat.succ (f a a)) in begin
  have : f a a = nat.succ (f a a) := congr_fun ha _,
  exact nat.succ_ne_self _ this.symm,

end
#print h


#exit
import data.multiset

def value_aux' (N_min : multiset ℕ → ℕ) : multiset ℕ → multiset ℕ → ℕ
| C L := N_min (multiset.pmap
  (λ a (h : a ∈ C),
    have multiset.card (C.erase a) < multiset.card C,
      from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
    a - 2 + int.nat_abs (2 - value_aux' (C.erase a) L))
    C (λ _,id) + multiset.pmap
  (λ a (h : a ∈ L),
    have multiset.card (L.erase a) < multiset.card L,
      from multiset.card_lt_of_lt (multiset.erase_lt.2 h),
    a - 4 +int.nat_abs (4 - value_aux' C (L.erase a)))
    L (λ _,id))
using_well_founded {rel_tac := λ _ _,
  `[exact ⟨_, measure_wf (λ CL, multiset.card CL.fst + multiset.card CL.snd)⟩]}

set_option pp.proofs true
#print value_aux'._main._pack
#exit
example (C : multiset ℕ) : decidable (∃ a : ℕ, a ≥ 4 ∧ a ∈ C) :=
suffices this : decidable (∃ a ∈ C, a ≥ 4),
by { resetI, apply @decidable_of_iff _ _ _ this, apply exists_congr, intro, tauto },
by { apply_instance }

set_option pp.implicit true
instance decidable_exists_multiset {α : Type*} (s : multiset α) (p : α → Prop) [decidable_pred p] :
  decidable (∃ x ∈ s, p x) :=
quotient.rec_on s list.decidable_exists_mem (λ a b h, subsingleton.elim _ _)

example (C : multiset ℕ) : decidable (∃ a : ℕ, a ≥ 4 ∧ a ∈ C) :=
decidable_of_iff (∃ a ∈ quotient.out C, a ≥ 4) (⟨λ ⟨x, hx₁, hx₂⟩, ⟨x, hx₂, begin
  rw ← quotient.out_eq C,
  exact hx₁,
end⟩, λ ⟨x, hx₁, hx₂⟩, ⟨x, begin
  rw ← quotient.out_eq C at hx₂,
  exact ⟨ hx₂, hx₁⟩
end⟩⟩)

#exit
import data.num.basic import tactic.basic data.num.lemmas data.list.basic data.complex.basic
open tactic

namespace ring_tac
open tactic

-- We start by modelling polynomials as lists of integers. Note that znum
-- is basically the same as int, but optimised for computations.

-- The list [a0,a1,...,an] represents a0 + a1*x + a2*x^2 + ... +an*x^n

def poly := list znum

-- We now make basic definitions and prove basic lemmas about addition of polynomials,
-- multiplication of a polynomial by a scalar, and multiplication of polynomials.

def poly.add : poly → poly → poly
| [] g := g
| f [] := f
| (a :: f') (b :: g') := (a + b) :: poly.add f' g'

@[simp] lemma poly.zero_add (p : poly) : poly.add [] p = p := by cases p; refl

def poly.smul : znum → poly → poly
| _ [] := []
| z (a :: f') := (z * a) :: poly.smul z f'

def poly.mul : poly → poly → poly
| [] _ := []
| (a :: f') g := poly.add (poly.smul a g) (0 :: poly.mul f' g)

def poly.const : znum → poly := λ z, [z]

def poly.X : poly := [0,1]

-- One problem with our implementation is that the lists [1,2,3] and [1,2,3,0] are different
-- list, but represent the same polynomial. So we define an "is_equal" predicate.

def poly.is_eq_aux : list znum -> list znum -> bool
| [] [] := tt
| [] (h₂ :: t₂) := if (h₂ = 0) then poly.is_eq_aux [] t₂ else ff
| (h₁ :: t₁) [] := if (h₁ = 0) then poly.is_eq_aux t₁ [] else ff
| (h₁ :: t₁) (h₂ :: t₂) := if (h₁ = h₂) then poly.is_eq_aux t₁ t₂ else ff

def poly.is_eq : poly → poly → bool := poly.is_eq_aux

-- evaluation of a polynomial at some element of a commutative ring.
def poly.eval {α} [comm_ring α] (X : α) : poly → α
| [] := 0
| (n::l) := n + X * poly.eval l

-- Lemmas saying that evaluation plays well with addition, multiplication, polynomial equality etc

@[simp] lemma poly.eval_zero {α} [comm_ring α] (X : α) : poly.eval X [] = 0 := rfl

@[simp] theorem poly.eval_add {α} [comm_ring α] (X : α) : ∀ p₁ p₂ : poly,
  (p₁.add p₂).eval X = p₁.eval X + p₂.eval X :=
begin
  intro p₁,
  induction p₁ with h₁ t₁ H,
    -- base case
    intros,simp [poly.eval],
  -- inductive step
  intro p₂,
  cases p₂ with h₂ t₂,
    simp [poly.add],
  unfold poly.eval poly.add,
  rw (H t₂),
  simp [mul_add]
end

@[simp] lemma poly.eval_mul_zero {α} [comm_ring α] (f : poly) (X : α) :
  poly.eval X (poly.mul f []) = 0 :=
begin
  induction f with h t H,
    refl,
  unfold poly.mul poly.smul poly.add poly.mul poly.eval,
  rw H,simp
end

@[simp] lemma poly.eval_smul {α} [comm_ring α] (X : α) (z : znum) (f : poly) :
  poly.eval X (poly.smul z f) = z * poly.eval X f :=
begin
  induction f with h t H, simp [poly.smul,poly.eval,mul_zero],
  unfold poly.smul poly.eval,
  rw H,
  simp [mul_add,znum.cast_mul,mul_assoc,mul_comm]
end

@[simp] theorem poly.eval_mul {α} [comm_ring α] (X : α) : ∀ p₁ p₂ : poly,
  (p₁.mul p₂).eval X = p₁.eval X * p₂.eval X :=
begin
  intro p₁,induction p₁ with h₁ t₁ H,
    simp [poly.mul],
  intro p₂,
  unfold poly.mul,
  rw poly.eval_add,
  unfold poly.eval,
  rw [H p₂,znum.cast_zero,zero_add,add_mul,poly.eval_smul,mul_assoc]
end

@[simp] theorem poly.eval_const {α} [comm_ring α] (X : α) : ∀ n : znum,
  (poly.const n).eval X = n :=
begin
  intro n,
  unfold poly.const poly.eval,simp
end

@[simp] theorem poly.eval_X {α} [comm_ring α] (X : α) : poly.X.eval X = X :=
begin
  unfold poly.X poly.eval,simp
end

-- Different list representing the same polynomials evaluate to the same thing
theorem poly.eval_is_eq {α} [comm_ring α] (X : α) {p₁ p₂ : poly} :
  poly.is_eq p₁ p₂ → p₁.eval X = p₂.eval X :=
begin
  revert p₂,
  induction p₁ with h₁ t₁ H₁,
  { intros p₂ H,
    induction p₂ with h₁ t₁ H₂,refl,
    unfold poly.eval,
    unfold poly.is_eq poly.is_eq_aux at H,
    split_ifs at H,swap,cases H,
    rw [h,←H₂ H],
    simp },
  { intros p₂ H,
    induction p₂ with h₂ t₂ H₂,
    { unfold poly.eval,
      unfold poly.is_eq poly.is_eq_aux at H,
      split_ifs at H,swap,cases H,
      rw [h,H₁ H],
      simp },
    { unfold poly.eval,
      unfold poly.is_eq poly.is_eq_aux at H,
      split_ifs at H,swap,cases H,
      unfold poly.is_eq at H₂,
      rw [h,H₁ H] } }

end

-- That's the end of the poly interface. We now prepare for the reflection.

-- First an abstract version of polynomials (where equality is harder to test, and we won't
-- need to test it). We'll construct a term of this type from (x+1)*(x+1)*(x+1)

-- fancy attribute because we will be using reflection in meta-land
@[derive has_reflect]
inductive ring_expr : Type
| add : ring_expr → ring_expr → ring_expr
| mul : ring_expr → ring_expr → ring_expr
| const : znum → ring_expr
| X : ring_expr
-- Now a "reflection" of this abstract type which the VM can play with.
meta def reflect_expr (X : expr) : expr → option ring_expr
| `(%%e₁ + %%e₂) := do
  p₁ ← reflect_expr e₁,
  p₂ ← reflect_expr e₂,
  return (ring_expr.add p₁ p₂)
| `(%%e₁ * %%e₂) := do
  p₁ ← reflect_expr e₁,
  p₂ ← reflect_expr e₂,
  return (ring_expr.mul p₁ p₂)
| e := if e = X then return ring_expr.X else
  do n ← expr.to_int e,
    return (ring_expr.const (znum.of_int' n))

-- turning the abstract poly into a concrete list of coefficients.
def to_poly : ring_expr → poly
| (ring_expr.add e₁ e₂) := (to_poly e₁).add (to_poly e₂)
| (ring_expr.mul e₁ e₂) := (to_poly e₁).mul (to_poly e₂)
| (ring_expr.const z) := poly.const z
| ring_expr.X := poly.X

-- evaluating the abstract poly
def ring_expr.eval {α} [comm_ring α] (X : α) : ring_expr → α
| (ring_expr.add e₁ e₂) := e₁.eval + e₂.eval
| (ring_expr.mul e₁ e₂) := e₁.eval * e₂.eval
| (ring_expr.const z) := z
| ring_expr.X := X

-- evaluating the abstract and the concrete polynomial gives the same answer
theorem to_poly_eval {α} [comm_ring α] (X : α) (e) : (to_poly e).eval X = e.eval X :=
by induction e; simp [to_poly, ring_expr.eval, *]

-- The big theorem! If the concrete polys are equal then the abstract ones evaluate
-- to the same value.
theorem main_thm {α} [comm_ring α] (X : α) (e₁ e₂) {x₁ x₂}
  (H : poly.is_eq (to_poly e₁) (to_poly e₂)) (R1 : e₁.eval X = x₁) (R2 : e₂.eval X = x₂) : x₁ = x₂ :=
by rw [← R1, ← R2, ← to_poly_eval,poly.eval_is_eq X H, to_poly_eval]

-- Now here's the tactic! It takes as input the unknown but concrete variable x
-- and an expression f(x)=g(x),
-- creates abstract polys f(X) and g(X), proves they're equal using rfl,
-- and then applies the main theorem to deduce f(x)=g(x).

meta def ring_tac (X : pexpr) : tactic unit := do
  X ← to_expr X,
  `(%%x₁ = %%x₂) ← target,
  r₁ ← reflect_expr X x₁,
  r₂ ← reflect_expr X x₂,
  let e₁ : expr := reflect r₁,
  let e₂ : expr := reflect r₂,
  `[refine main_thm %%X %%e₁ %%e₂ rfl _ _],
  all_goals `[simp only [ring_expr.eval,
    znum.cast_pos, znum.cast_neg, znum.cast_zero',
    pos_num.cast_bit0, pos_num.cast_bit1,
    pos_num.cast_one']]

example (x : ℤ) : (x + 1) * (x + 1) = x*x+2*x+1 := by do ring_tac ```(x)

example (x : ℤ) : (x + 1) * (x + 1) * (x + 1) = x*x*x+3*x*x+3*x+1 := by do ring_tac ```(x)

example (x : ℤ) : (x + 1) + ((-1)*x + 1) = 2 := by do ring_tac ```(x)

end ring_tac

def poly := list znum

def poly.add : poly → poly → poly
| [] g := g
| f [] := f
| (a :: f') (b :: g') := (a + b) :: poly.add f' g'

def poly.eval {α} [comm_ring α] (X : α) : poly → α
| [] := 0
| (n::l) := n + X * poly.eval l

#exit
open expr tactic classical


section logical_equivalences
local attribute [instance] prop_decidable
variables {a b : Prop}
theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
iff.intro classical.by_contradiction not_not_intro
theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
iff.intro
(λ h, if ha : a then or.inr (h ha) else or.inl ha)
(λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))
theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)
theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
if ha : a then
or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
else
or.inl ha
theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
iff.intro not_or_not_of_not_and not_and_of_not_or_not
theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
assume h1, or.elim h1 (assume ha, h^.left ha) (assume hb, h^.right hb)
theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
iff.intro not_and_not_of_not_or not_or_of_not_and_not
end logical_equivalences

meta def normalize_hyp (lemmas : list expr) (hyp : expr) : tactic unit :=
do try (simp_at hyp lemmas)

meta def normalize_hyps : tactic unit :=
do hyps ← local_context,
lemmas ← monad.mapm mk_const [``iff_iff_implies_and_implies,
``implies_iff_not_or, ``not_and_iff, ``not_or_iff, ``not_not_iff,
``not_true_iff, ``not_false_iff],
monad.for' hyps (normalize_hyp lemmas)

#exit
def bind_option {X : Type} {Y : Type} :
  option X → (X → option Y) → option Y
| option.none f := @option.none Y
| (option.some x) f := f x

#print option.bind

lemma pierce_em : (∀ p q : Prop, ((p → q) → p) → p) ↔ (∀ p, p ∨ ¬p) :=
⟨λ pierce p, pierce (p ∨ ¬p) (¬p) (λ h, or.inr (λ hp, h (or.inl hp) hp)),
λ em p q, (em p).elim (λ hp _, hp)
  (λ h h₁, h₁ $ (em q).elim (λ hq _, hq) (λ h₂ hp, (h hp).elim))⟩

#print axioms pierce_em

lemma double_neg_em : (∀ p, ¬¬p → p) ↔ (∀ p, p ∨ ¬p) :=
⟨λ dneg p, dneg () (λ h, h (or.inr (h ∘ or.inl))),
λ em p hneg, (em p).elim id (λ h, (hneg h).elim)⟩

#print axioms double_neg_em

lemma demorgan_em : (∀ p q, ¬ (¬p ∧ ¬q) → p ∨ q) ↔ (∀ p, p ∨ ¬p) :=
⟨λ h p, h p (¬p) (λ h, h.2 h.1),
λ em p q h, (em p).elim or.inl $ λ not_p, (em q).elim or.inr
  (λ not_q, (h ⟨not_p, not_q⟩).elim)⟩

#print axioms demorgan_em

lemma implies_to_or_em : (∀ p q, (p → q) → (¬p ∨ q)) ↔ (∀ p, p ∨ ¬p) :=
⟨λ h p, or.symm $ h p p id,
λ em p q hpq, (em p).elim (or.inr ∘ hpq) or.inl⟩

#print axioms implies_to_or_em

#exit
import logic.function data.equiv.basic
open function
universe u
axiom exists_inv_of_bijection {α β : Sort*} {f : α → β}
  (hf : bijective f) : ∃ g : β → α, left_inverse f g ∧ right_inverse f g

axiom em2 (p : Prop) : p ∨ ¬p

lemma choice2 {α : Sort*} : nonempty (nonempty α → α) :=
(em2 (nonempty α)).elim
(λ ⟨a⟩, ⟨λ _, a⟩) (λ h, ⟨false.elim ∘ h⟩)

lemma choice3 : nonempty (Π {α : Sort u}, nonempty α → α) :=
(em2 (nonempty (Π {α : Sort u}, nonempty α → α))).elim id
(λ h, begin

end)


lemma choice_equiv :
  (∀ {α : Sort*}, nonempty (nonempty α → α)) → (nonempty)

lemma exists_inv_of_bijection {α β : Sort*} {f : α → β}
  (hf : bijective f) : ∃ g : β → α, left_inverse f g ∧ right_inverse f g :=
have hchoice : ∀ b : β, nonempty (nonempty {a : α // f a = b} → {a : α // f a = b}) :=
  λ b, choice2,
let choice : Π b : β, nonempty {a : α // f a = b} → {a : α // f a = b} :=
λ b, begin end in

let f : Π b : β, {a : α // f a = b} := λ b, begin end,
begin
  cases hf,


end

example {α : Sort*} : nonempty (nonempty α → α) :=
begin

end

lemma em2 {p : Prop} : p ∨ ¬p :=
let U : Prop → Prop := λ q, q = true ∨ p in
let V : Prop → Prop := λ q, q = false ∨ p in

have u : subtype U := ⟨true, or.inl rfl⟩,
have v : subtype V := ⟨false, or.inl rfl⟩,
have not_uv_or_p : u.1 ≠ v.1 ∨ p :=
  u.2.elim (v.2.elim (λ h₁ h₂, h₁.symm ▸ h₂.symm ▸ or.inl (λ htf, htf ▸ ⟨⟩))
  (λ hp _, or.inr hp)) or.inr,
have p_implies_uv : p → u.1 = v.1 := λ hp,
have U = V := funext (assume x : Prop,
  have hl : (x = true ∨ p) → (x = false ∨ p), from
    assume a, or.inr hp,
  have hr : (x = false ∨ p) → (x = true ∨ p), from
    assume a, or.inr hp,
  show (x = true ∨ p) = (x = false ∨ p), from
    propext (iff.intro hl hr)),
begin

end,
begin

end,
not_uv_or_p.elim
  (λ h, or.inr $ mt p_implies_uv h)
  or.inl




#exit
import tactic.interactive
namespace tactic



run_cmd mk_simp_attr `norm_num2

lemma two_add_three : 2 + 3 = 4 := sorry

attribute [norm_num2] two_add_three

meta def norm_num2 : tactic unit :=
  do simp_all

meta def generalize_proofs (ns : list name) : tactic unit :=
do intros_dep,
   hs ← local_context >>= mfilter is_proof,
   t ← target,
   collect_proofs_in t [] (ns, hs) >> skip

theorem not_not_iff (a : Prop) : ¬¬a ↔ a :=
iff.intro classical.by_contradiction not_not_intro

theorem implies_iff_not_or (a b : Prop) : (a → b) ↔ (¬ a ∨ b) :=
iff.intro
(λ h, if ha : a then or.inr (h ha) else or.inl ha)
(λ h, or.elim h (λ hna ha, absurd ha hna) (λ hb ha, hb))

theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b) :=
assume ⟨ha, hb⟩, or.elim h (assume hna, hna ha) (assume hnb, hnb hb)

theorem not_or_not_of_not_and (h : ¬ (a ∧ b)) : ¬ a ∨ ¬ b :=
if ha : a then
or.inr (show ¬ b, from assume hb, h ⟨ha, hb⟩)
else
or.inl ha

theorem not_and_iff (a b : Prop) : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
iff.intro not_or_not_of_not_and not_and_of_not_or_not

theorem not_or_of_not_and_not (h : ¬ a ∧ ¬ b) : ¬ (a ∨ b) :=
assume h1, or.elim h1 (assume ha, h^.left ha) (assume hb, h^.right hb)

theorem not_and_not_of_not_or (h : ¬ (a ∨ b)) : ¬ a ∧ ¬ b :=
and.intro (assume ha, h (or.inl ha)) (assume hb, h (or.inr hb))

theorem not_or_iff (a b : Prop) : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
iff.intro not_and_not_of_not_or not_or_of_not_and_not
end logical_equivalences

meta def normalize_hyp (lemmas : simp_lemmas) (lemmas2 : list name) (hyp : expr) : tactic unit :=
do try (simp_hyp lemmas lemmas2 hyp)

meta def normalize_hyps : tactic unit :=
do hyps ← local_context,
lemmas ← monad.mapm mk_const [``iff_iff_implies_and_implies,
``implies_iff_not_or, ``not_and_iff, ``not_not_iff,
``not_true_iff, ``not_false_iff],
 hyps (normalize_hyp lemmas)


open tactic
universe u

meta def find_same_type : expr → list expr → tactic expr
| e [] := failed
| e (h :: hs) :=
do t ← infer_type h,
(unify e t >> return h) <|> find_same_type e hs

meta def assumption : tactic unit :=
do ctx ← local_context,
t ← target,
h ← tactic.find_same_type t ctx,
exact h
<|> fail "assumption tactic failed"

#print assumption
#print nonempty


#print eq_of_heq

variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable  log_exp_eq : ∀ x, log (exp x) = x
variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable  exp_pos    : ∀ x, exp x > 0
variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0)  : exp (log y) = y :=
exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc
    log (x * y) = log (exp (log x) * exp(log y))   : by rw [← exp_log_eq hx, ← exp_log_eq hy]
    ...         = log (exp (log x + log y))        : by rw [← exp_add (log x) (log y)]
    ...         = log x + log y                    : by rw [log_exp_eq (log x + log y)]
example : ∀ {α : Sort u} {a a' : α}, a == a' → a = a' :=
λ α a a' h, @heq.rec_on α a (λ β b, begin end) h begin


end

example (a b : Prop) (h : a ∧ b) : b ∧ a :=
by do split,
eh ← get_local `h,
mk_const ``and.right >>= apply,
exact eh,
mk_const ``and.left >>= apply,
exact eh

namespace foo
theorem bar : true := trivial
meta def my_tac : tactic unit :=
mk_const ``bar >>= exact

example : true := by my_tac

end foo

#print apply_instance
lemma h : a → b → a ∧ b :=
by do eh1 ← intro `h1,
eh2 ← intro `h2,
applyc ``and.intro,
exact eh1,
exact eh2

#print h

universes u v
open io



#eval put_str "hello " >> put_str "world! " >> put_str (to_string (27 * 39))

#eval (some 2) <|> (some 1)

#print axioms put_str
#check @put_str
#check @get_line

namespace la
structure registers : Type := (x : ℕ) (y : ℕ) (z : ℕ)
def init_reg : registers := registers.mk 0 0 0

def state (S : Type u) (α : Type v) : Type (max u v) := S → α × S

instance (S : Type u) : monad (state S) :=
{ pure := λ α a r, (a, r),
  bind := λ α β sa b s, b (sa s).1 (sa s).2 }

def read {S : Type} : state S S :=
λ s, (s, s)

def write {S : Type} : S → state S unit :=
λ s0 s, ((), s0)

@[reducible] def reg_state := state registers

def read_x : reg_state ℕ :=
do s ← read, return (registers.x s)

def read_y : reg_state ℕ :=
do s ← read, return (registers.y s)

def read_z : reg_state ℕ :=
do s ← read, return (registers.z s)

def write_x (n : ℕ) : reg_state unit :=
do s ← read,
write (registers.mk n (registers.y s) (registers.z s))

def write_y (n : ℕ) : reg_state unit :=
do s ← read,
write(registers.mk (registers.x s) n (registers.z s))

def write_z (n : ℕ) : reg_state unit :=
do s ← read,
write (registers.mk (registers.x s) (registers.y s) n)

def foo : reg_state ℕ :=
do  write_x 5,
    write_y 7,
    x ← read_x,
    write_z (x + 3),
    y ← read_y,
    z ← read_z,
    write_y (y + z),
    y ← read_y,
    return (y ^ 3)

#print foo

end la
#exit

universe u
variables {α β γ δ : Type.{u}} (la : list α)
variables (f : α → list β) (g : α → β → list γ)
(h : α → β → γ → list δ)

inductive option2 (α : Type u) : Type u
| none : option2
| some : α → option2

instance : monad option2 :=
begin
  refine {..},
  refine λ α β, _,

end

#print applicative
#print option.monad
example : list δ :=
do a ← la,
b ← f a,
c ← g a b,


#exit
import data.multiset data.finset order.bounded_lattice

@[derive decidable_eq] structure sle :=
(three_chains : ℕ) -- number of three-chains
(four_loops : ℕ)
(six_loops : ℕ)
(long_chains : multiset ℕ)
(long_chains_are_long : ∀ x ∈ long_chains, x ≥ 4)
(long_loops : multiset ℕ)
(long_loops_are_long : ∀ x ∈ long_loops, x ≥ 8)
(long_loops_are_even : ∀ x ∈ long_loops, 2 ∣ x)

def size (e : sle) : ℕ := sorry

def legal_moves (e : sle) : finset {f : sle // size f < size e} := sorry

def val : sle → with_top ℕ
| e := (legal_moves e).inf
  (λ f, have size f.1 < size e := f.2, (val f.1 : with_top ℕ))
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf size⟩]}

def val2 : Π e : sle, legal_moves e ≠ ∅ → ℕ
| e := (legal_moves e).inf
  (λ f, have size f.1 < size e := f.2, (val f.1 : with_top ℕ))

#exit

variables {α β γ δ : Type.{u}} (oa : option α)
variables (f : α → option β) (g : α → β → option γ)
(h : α → β → γ → option δ)

definition test (m : Type → Type) [monad m]
  (α : Type) (s : m α) (β : Type) (t : m β) (γ : Type) (f : α → β → m γ)
  (g : α → β → m γ)
  :=
do a ← s,
b ← t,
return (g a b)

def x : option β :=
do a ← oa,
   b ← f a,
   return b

#print x

example : option δ :=
do a ← oa,
b ← f a,
c ← g a b,
h a b c

#print option.return


@[elab_as_eliminator, elab_strategy] def multiset.strong_induction_on2 {α : Type*} {p : multiset α → Sort*} :
  ∀ (s : multiset α), (∀ s, (∀t < s, p t) → p s) → p s :=
well_founded.fix (measure_wf multiset.card) (λ s ih h, h s (λ t ht, ih t (multiset.card_lt_of_lt ht) h))

#print multiset.strong_induction_on2
definition f (s : multiset ℕ) : ℕ :=
  multiset.strong_induction_on2 s (λ s' H, 0)

#eval f ({1,2,3} : multiset ℕ)

def bar : ℕ → ℕ
| 0     := 0
| (n+1) := list.length
  (list.pmap (λ m (hm : m < n + 1), bar m) [n, n, n]
  (by simp [nat.lt_succ_self]))

set_option pp.proofs true
#print bar._main._pack

def map_rec_on {C : ℕ → Sort*} (f : ℕ → list ℕ) :
  Π (n : ℕ) (h : ∀ m, ∀ k ∈ f m, k < m)
  (c0 : C 0) (ih : (Π n, list ℕ → C (n + 1))), C n
| 0 := λ h c0 ih, c0
| (n+1) := λ h c0 ih, begin have := ih n,
   have := this ((f (n + 1)).map (λ m, map_rec_on,

 end

#eval bar 1

def bar_aux : ℕ → (ℕ → list ℕ) → list ℕ
| 0 _   := []
| (n+1) f := list.repeat 3 $
  list.length (bar_aux n f)

#eval bar_aux 2 (λ n, [n, n, n])

instance subtype.has_decidable_eq (α : Prop) [h : decidable_eq α]
  (p : α → Prop) : decidable_eq (subtype p)
| ⟨_, _⟩ ⟨_, _⟩ := is_true rfl
#print decidable

lemma h (p : Prop) : ¬(p ↔ ¬p) :=
λ h : p ↔ ¬p,
have not_p : ¬p := λ hp : p, h.1 hp hp,
not_p (h.2 not_p)

#print h

def subfunc_to_option {α β: Type} {c: α → Prop} [decidable_pred c]
(f: {x:α // c x} → β) : α → option β :=
λ y: α, if h : c y then some (f (subtype.mk y h)) else none

def option_to_subfunc {α β: Type} (f: α → (option β)) :
  {x : α // option.is_some (f x)} → β | ⟨x, h⟩ := option.get h

theorem inv1 {α β: Type} {c: α → Prop} (f: {x:α // c x} → β) [decidable_pred c] :
∀ y : {x // c x}, option_to_subfunc (@subfunc_to_option α β c _ f) ⟨y.1, sorry⟩ = f y := sorry
#print roption
def option_to_subfunc {α β: Type} (f: α → (option β)) :
  {x : α // f x ≠ none} → β :=
λ y: {x:α // f x ≠ none},
match f y, y.2 with
| some x, hfy := x
| none  , hfy := (hfy rfl).elim
end

def subfunc_to_option {α β: Type} {c: α → Prop} [decidable_pred c]
(f: {x:α // c x} → β) : α → option β :=
λ y: α, if h : c y then some (f (subtype.mk y h)) else none

open lattice
variable {α : Type*}

lemma sup_eq_max [decidable_linear_order α] (a b : with_bot α) : a ⊔ b = max a b :=
le_antisymm (sup_le (le_max_left _ _) (le_max_right _ _)) (max_le le_sup_left le_sup_right)

lemma inf_eq_min [decidable_linear_order α] (a b : with_top α) : a ⊓ b = min a b :=
le_antisymm (le_min inf_le_left inf_le_right) (le_inf (min_le_left _ _) (min_le_right _ _))

#print subtype.eq

#print subtype.eq

lemma well_founded_lt_with_bot {α : Type*} [partial_order α] (h : well_founded ((<) : α → α → Prop)) :
  well_founded ((<) : with_bot α → with_bot α → Prop) :=
have acc_bot : acc ((<) : with_bot α → with_bot α → Prop) ⊥ :=
  acc.intro _ (λ a ha, (not_le_of_gt ha bot_le).elim),
⟨λ a, option.rec_on a acc_bot (λ a, acc.intro _ (λ b, option.rec_on b (λ _, acc_bot)
(λ b, well_founded.induction h b
  (show ∀ b : α, (∀ c, c < b → (c : with_bot α) < a →
      acc ((<) : with_bot α → with_bot α → Prop) c) → (b : with_bot α) < a →
        acc ((<) : with_bot α → with_bot α → Prop) b,
  from λ b ih hba, acc.intro _ (λ c, option.rec_on c (λ _, acc_bot)
    (λ c hc, ih _ (with_bot.some_lt_some.1 hc) (lt_trans hc hba)))))))⟩

lemma well_founded_lt_with_top {α : Type*} [partial_order α] (h : well_founded ((<) : α → α → Prop)) :
  well_founded ((<) : with_top α → with_top α → Prop) :=
have acc_some : ∀ a : α, acc ((<) : with_top α → with_top α → Prop) (some a) :=
λ a, acc.intro _ (well_founded.induction h a
  (show ∀ b, (∀ c, c < b → ∀ d : with_top α, d < some c → acc (<) d) →
    ∀ y : with_top α, y < some b → acc (<) y,
  from λ b ih c, option.rec_on c (λ hc, (not_lt_of_ge lattice.le_top hc).elim)
    (λ c hc, acc.intro _ (ih _ (with_top.some_lt_some.1 hc))))),
⟨λ a, option.rec_on a (acc.intro _ (λ y, option.rec_on y (λ h, (lt_irrefl _ h).elim)
  (λ _ _, acc_some _))) acc_some⟩

#exit

variables {α : Type}

def preimage (f : α → ℕ) (u : ℕ) : set α  := λ x, f x=u

instance [fintype α] [decidable_eq α] (f : α → ℕ) (u : ℕ) : fintype (preimage f u) :=
by unfold preimage; apply_instance

def card_image [fintype α] [decidable_eq α] (f : α → ℕ) (u : ℕ) : ℕ :=
fintype.card (preimage f u)


#exit
variables {α β γ : Type}

-- function f is continuous at point x
axiom continuous_at (x : α) (f : α → β) : Prop

def continuous (f : α → β) : Prop := ∀ x, continuous_at x f

lemma continuous_comp (f : α → β) (g : β → γ) :
  continuous f → continuous g → continuous (g ∘ f) :=
begin
  assume cf cg x,
  unfold continuous at *,
  have := cg (f x)
end
#exit
import data.fintype.basic data.num.lemmas tactic.norm_num data.real.basic
#print prefix subsingleton

@[elab_with_expected_type] lemma subsingleton_thing {α : Type*} [subsingleton α] {P : α → Prop} (a : α)
  (h : P a) (b : α) : P b :=
by rwa subsingleton.elim b a

example {α : Type*} [f₁ : fintype α] (h : fintype.card α = 0) (f₂ : fintype α) :
  @fintype.card α f₂ = 0 :=
@subsingleton_thing (fintype α) _ _ f₁ h _

#print finset.product

lemma e : (2 : ℝ) + 2 = 4 := rfl

#print e
#exit
import data.equiv

def is_valuation {R : Type} [comm_ring R] {α : Type} [linear_order α] (f : R → α) : Prop := true

structure valuations (R : Type) [comm_ring R] :=
(α : Type) [Hα : linear_order α] (f : R → α) (Hf : is_valuation f)

instance to_make_next_line_work (R : Type) [comm_ring R] (v : valuations R) : linear_order v.α := v.Hα

instance valuations.setoid (R : Type) [comm_ring R] : setoid (valuations R) := {
  r := λ v w, ∀ r s : R, valuations.f v r ≤ v.f s ↔ w.f r ≤ w.f s,
  iseqv := ⟨λ v r s,iff.rfl,λ v w H r s,(H r s).symm,λ v w x H1 H2 r s,iff.trans (H1 r s) (H2 r s)⟩
}

def Spv1 (R : Type) [comm_ring R] := quotient (valuations.setoid R)

def Spv2 (R : Type) [comm_ring R] :=
  {ineq : R → R → Prop // ∃ v : valuations R, ∀ r s : R, ineq r s ↔ v.f r ≤ v.f s}

#check Spv1 _ -- Type 1
#check Spv2 _ -- Type

def to_fun (R : Type) [comm_ring R] : Spv1 R → Spv2 R :=
quotient.lift (λ v, (⟨λ r s, valuations.f v r ≤ v.f s, ⟨v,λ r s,iff.rfl⟩⟩ : Spv2 R))
  (λ v w H,begin dsimp,congr,funext,exact propext (H r s) end)

open function
noncomputable definition they_are_the_same (R : Type) [comm_ring R] : equiv (Spv1 R) (Spv2 R) :=
equiv.of_bijective $ show bijective (to_fun R),
from ⟨λ x y, quotient.induction_on₂ x y $ λ x y h,
  quotient.sound $ λ r s, iff_of_eq $ congr_fun (congr_fun (subtype.mk.inj h) r) s,
  λ ⟨x, ⟨v, hv⟩⟩, ⟨⟦v⟧, subtype.eq $ funext $ λ r, funext $ λ s, propext (hv r s).symm⟩⟩

noncomputable definition they_are_the_same (R : Type) [comm_ring R] : equiv (Spv1 R) (Spv2 R) :=
{ to_fun := to_fun R,
  inv_fun := inv_fun R,
  left_inv := λ vs, quotient.induction_on vs begin
    assume vs,
    apply quotient.sound,
    intros r s,
    have := (to_fun R ⟦vs⟧).property,
    have H := classical.some_spec (to_fun R ⟦vs⟧).property r s,
    refine H.symm.trans _,
    refl,
  end,
  right_inv := λ s2,begin
    cases s2 with rel Hrel,
    apply subtype.eq,
    dsimp,
    unfold inv_fun,
    funext r s,
    sorry
  end
}

#exit
import logic.function data.set.basic set_theory.cardinal
universes u v w x
open function

lemma eq.rec_thing {α : Sort*} (a : α) (h : a = a) (C : α → Sort*) (b : C a) : (eq.rec b h : C a) = b := rfl

def T : Type 1 := Σ α : Type, set α

set_option trace.simplify.rewrite true
lemma Type_1_bigger {α : Type} {f : T → α} : ¬injective f :=
λ h, cantor_injective (f ∘ sigma.mk α) $ injective_comp h (by simp [injective])

theorem forall_2_true_iff2  {α : Sort u} {β : α → Sort v} : (∀ (a b : α), true) ↔ true :=
by rw [forall_true_iff, forall_true_iff]

theorem forall_2_true_iff3  {α : Sort u} {β : α → Sort v} : (∀ (a b : α), true) ↔ true :=
by simp only [forall_true_iff, forall_true_iff]

example {α : Type} {f : α → T} : ¬ surjective f :=
λ h, Type_1_bigger (injective_surj_inv h)

#exit
constant a : ℕ

lemma empty_implies_false (f : empty → empty) : f = id :=
funext $ λ x, by cases x

#print has_equiv

structure thing {R : Type} [ring R]
{ type : Type }
(  )

instance : has_repr pnat := subtype.has_repr

#eval ((@function.comp ℕ ℕ ℕ) ∘ (∘))

#print quotient.lift_on
noncomputable example (f : α → β) :
  quotient (fun_rel f) ≃ set.range f :=
@equiv.of_bijective _ _ (λ a, @quotient.lift_on _ _ (fun_rel f) a
(λ a, show set.range f, from ⟨f a, set.mem_range_self _⟩)
(λ a b h, subtype.eq h))
⟨λ a b, @quotient.induction_on₂ _ _ (fun_rel f) (fun_rel f) _ a b begin
  assume a b h,
  exact quot.sound (subtype.mk.inj h),
end, λ ⟨a, ⟨x, ha⟩⟩, ⟨@quotient.mk _ (fun_rel f) x, by simp * ⟩⟩

noncomputable example {G H : Type*} [group G] [group H] (f : G → H) [is_group_hom f] :
  {x : left_cosets (ker f) ≃ set.range f // is_group_hom x} :=
⟨@equiv.of_bijective _ _ (λ a, @quotient.lift_on _ _ (left_rel (ker f)) a
  (λ a, show set.range f, from ⟨f a, set.mem_range_self _⟩)
    (λ a b h, subtype.eq begin
    show f a = f b,
    rw [← one_mul b, ← mul_inv_self a, mul_assoc, is_group_hom.mul f, mem_trivial.1 h, mul_one],
  end)) ⟨λ a b, @quotient.induction_on₂ _ _(left_rel (ker f)) (left_rel (ker f)) _ a b
  (begin
    assume a b h,
    have : f a = f b := subtype.mk.inj h,
    refine quot.sound (mem_trivial.2 _),
    rw [mul f, ← this, ← mul f, inv_mul_self, one f]
  end),
  λ ⟨a, ha⟩,
  let ⟨x, hx⟩ := set.mem_range.1 ha in
  ⟨@quotient.mk _ (left_rel (ker f)) x, subtype.eq hx⟩⟩,
  ⟨λ a b, @quotient.induction_on₂ _ _(left_rel (ker f)) (left_rel (ker f)) _ a b begin
    assume a b,
    rw equiv.of_bijective_to_fun,
    exact subtype.eq (mul f _ _),
  end⟩⟩
#print has_repr

instance : has_repr (finset α) :=

#exit
universes u v
axiom choice {α : Type u} (β : α → Type v)
  (h : ∀ a : α, nonempty (β a)) : Π a, β a

example {α : Type u} : nonempty α → α :=
λ h, @choice unit (λ _, α) (λ _, h) ()

#print classical.axiom_of_choice

variable (α : Type)
def foo : semigroup α :=
begin
  refine_struct { .. },
end
variables {a b c : ℕ}

#print empty.elim
lemma empty_implies_false (f : empty → empty) : f = id :=
#print empty_implies_false

#eval list.foldr ((∘) : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ) id [nat.succ, nat.pred] 0

example (x : ℕ) (l : list ℕ) : list.prod (x :: l) = l.prod * x := rfl

example : list.prod [a, b, c] = sorry := begin
  unfold list.prod list.foldl,

end

#print list.prod
open set
local attribute [instance] classical.prop_decidable
example (a b : Prop) : ((a → b) → (a ↔ b)) ↔ (b → a) :=
⟨λ h, begin
  by_cases A : b,
  simp [A, *] at *,
  simp [A, *] at *,


end,
begin
  intros; split; assumption
end⟩

-- so my goal is to define graphs
-- I find the best way to implement them is as a structure with a set of vertices and a binary relation on those vertices
-- I like the coercion from sets to subtypes, but it looks like it makes things a little complicated with the little experience I have (see below)

constants {V : Type} (vertices : set V) (edge : vertices → vertices → Prop)

-- this is an extra convenient definition to allow the creation of "set edges" below
def edges : set (vertices × vertices) := λ ⟨v₁,v₂⟩, edge v₁ v₂

-- I would like to reason on the edge binary relation rather than on the set of edges, that's why I suppose edge is a decidable rel
instance [H : decidable_rel edge] : decidable_pred edges := λ⟨v₁,v₂⟩, H v₁ v₂

-- set of edges whose tip is v ∈ vertices
-- used to define the "in-degree" of vertex v
-- in_edges has type "set edges" because I find it convenient, maybe it's not the best to do (too many coercions ?)
def in_edges (v : vertices) : set edges := let ⟨v,hv⟩ := v in λ⟨⟨_,⟨b,hb⟩⟩, _⟩, b = v

-- I need to use noncomputable because in_edges is a set whose base type is a subtype and
-- I only assume decidable_eq on V
-- but there exists subtype.decidable_eq...
#check subtype.decidable_eq

noncomputable instance [H : decidable_eq V] {v : vertices} : decidable_pred (in_edges v) := let ⟨v,hv⟩ := v in λ⟨⟨⟨a, ha⟩,⟨b,hb⟩⟩, _⟩, H b v
noncomputable instance {v : vertices} [fintype vertices] [decidable_rel edge] [decidable_eq V] : fintype (in_edges v) := @set_fintype _ (set_fintype _) _ _

variables [fintype vertices] [decidable_eq V] [decidable_rel edge]

-- now I want to define some stuff on finite graphs and prove some lemmas
-- for instance, the sum of the in_degrees of all the vertices is equal to fintype.card edges
-- which I did prove, but with another unpleasant setup
noncomputable def in_degree (v : vertices) := finset.card (in_edges v).to_finset
-- this doesn't work without the extra instances above
-- I would like instances to be inferred out-of-the-box but I didn't succeed

#exit
instance : fintype bool2 := bool.fintype

lemma card_bool1 : fintype.card bool2 = 2 :=
begin
  refl,
end

def bool2_fintype : fintype bool2 := ⟨{tt, ff}, λ x, by cases x; simp⟩

def bool2_fintype3 : fintype bool2 := ⟨{ff, tt}, λ x, by cases x; simp⟩

lemma card_bool2 : @fintype.card bool2 bool2_fintype = 2 :=
card_bool1 -- They are defeq

lemma card_bool3 : @fintype.card bool2 bool2_fintype = 2 :=
begin
  rw card_bool1, --doesn't work
end

lemma card_bool4 : @fintype.card bool2 bool2_fintype3 = 2 := card_bool1

#exit
#print rat.has_mul
def poly := list znum

def poly.is_eq_aux : list znum -> list znum -> bool
| [] [] := tt
| [] (h₂ :: t₂) := if (h₂ = 0) then poly.is_eq_aux [] t₂ else ff
| (h₁ :: t₁) [] := if (h₁ = 0) then poly.is_eq_aux t₁ [] else ff
| (h₁ :: t₁) (h₂ :: t₂) := if (h₁ = h₂) then poly.is_eq_aux t₁ t₂ else ff

def poly.is_eq : poly → poly → bool
| [] [] := tt
| [] (h₂ :: t₂) := if (h₂ = 0) then poly.is_eq [] t₂ else ff
| (h₁ :: t₁) [] := if (h₁ = 0) then poly.is_eq t₁ [] else ff
| (h₁ :: t₁) (h₂ :: t₂) := if (h₁ = h₂) then poly.is_eq t₁ t₂ else ff

#print default.sizeof

example (n : ℕ) : n ^ (n + 1) = sorry :=
begin
  simp [nat.pow_succ],
end

def normalizer (H : set G) : set G :=
{ g : G | ∀ n, n ∈ H ↔ g * n * g⁻¹ ∈ H }

instance (H : set G) [is_subgroup H] : is_subgroup (normalizer H) :=
{ one_mem := show ∀ n : G, n ∈ H ↔ 1 * n * 1⁻¹ ∈ H, by simp,
  mul_mem := λ a b (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H)
    (hb : ∀ n, n ∈ H ↔ b * n * b⁻¹ ∈ H) n,
    by rw [mul_inv_rev, ← mul_assoc, mul_assoc a, mul_assoc a, ← ha, hb],
  inv_mem := λ a (ha : ∀ n, n ∈ H ↔ a * n * a⁻¹ ∈ H) n,
    by rw [ha (a⁻¹ * n * a⁻¹⁻¹)];
    simp [mul_assoc] }

lemma subset_normalizer (H : set G) [is_subgroup H] : H ⊆ normalizer H :=
λ g hg n, by rw [is_subgroup.mul_mem_cancel_left _ ((is_subgroup.inv_mem_iff _).2 hg),
  is_subgroup.mul_mem_cancel_right _ hg]

instance (H : set G) [is_subgroup H] : normal_subgroup {x : normalizer H | ↑x ∈ H} :=
{ one_mem := show (1 : G) ∈ H, from is_submonoid.one_mem _,
  mul_mem := λ a b ha hb, show (a * b : G) ∈ H, from is_submonoid.mul_mem ha hb,
  inv_mem := λ a ha, show (a⁻¹ : G) ∈ H, from is_subgroup.inv_mem ha,
  normal := λ a ha ⟨m, hm⟩, (hm a).1 ha }

local attribute [instance] left_rel normal_subgroup.to_is_subgroup

instance : group (left_cosets H) :=
{ one := ⟦1⟧,
  mul := λ a b, quotient.lift_on₂ a b
  (λ a b, ⟦a * b⟧)
  (λ a₁ a₂ b₁ b₂ (hab₁ : a₁⁻¹ * b₁ ∈ H) (hab₂ : a₂⁻¹ * b₂ ∈ H),
    quotient.sound
    ((is_subgroup.mul_mem_cancel_left H (is_subgroup.inv_mem hab₂)).1
        (by rw [mul_inv_rev, mul_inv_rev, ← mul_assoc (a₂⁻¹ * a₁⁻¹),
          mul_assoc _ b₂, ← mul_assoc b₂, mul_inv_self, one_mul, mul_assoc (a₂⁻¹)];
          exact normal_subgroup.normal _ hab₁ _))),
  mul_assoc := λ a b c, quotient.induction_on₃
    a b c (λ a b c, show ⟦_⟧ = ⟦_⟧, by rw mul_assoc),
  one_mul := λ a, quotient.induction_on a
    (λ a, show ⟦_⟧ = ⟦_⟧, by rw one_mul),
  mul_one := λ a, quotient.induction_on a
    (λ a, show ⟦_⟧ = ⟦_⟧, by rw mul_one),
  inv := λ a, quotient.lift_on a (λ a, ⟦a⁻¹⟧)
    (λ a b hab, quotient.sound begin
      show a⁻¹⁻¹ * b⁻¹ ∈ H,
      rw ← mul_inv_rev,
      exact is_subgroup.inv_mem (is_subgroup.mem_norm_comm hab)
    end),
  mul_left_inv := λ a, quotient.induction_on a
    (λ a, show ⟦_⟧ = ⟦_⟧, by rw inv_mul_self) }


variables {I : Type*} (f : I → Type*)
open real
example : (sqrt 2 + sqrt 3) ^ 2 = 5 + 2 * sqrt 6 :=
begin
  rw [pow_two, mul_add, add_mul, add_mul, ← pow_two, ← pow_two, sqr_sqrt, sqr_sqrt,
    ← sqrt_mul, ← sqrt_mul],
    ring,
end

lemma g : 0.71 + 0.8 = 0.51 := rfl
#print g

example : (ℕ → fin 0) → false := λ f, nat.not_lt_zero (f 0).1 (f 0).2

instance semigroup1 [∀ i, semigroup $ f i] : semigroup (Π i : I, f i) :=
{ mul := begin intros, admit end,
mul_assoc := sorry
}

variables {α : Type*} {β : Type*}
noncomputable theory

namespace finset

lemma image_const [decidable_eq β] {s : finset α} (h : s ≠ ∅) (b : β) : s.image (λa, b) = singleton b :=
ext.2 $ assume b', by simp [exists_mem_of_ne_empty h, eq_comm]

@[simp] theorem max_singleton' [decidable_linear_order α] {a : α} : finset.max (singleton a) = some a :=
max_singleton

section Max
open option

variables [decidable_linear_order β] [inhabited β] {s : finset α} {f : α → β}

def maxi [decidable_linear_order β] [inhabited β] (s : finset α) (f : α → β) : β :=
(s.image f).max.iget

@[simp] lemma maxi_empty : (∅ : finset α).maxi f = default β := rfl

lemma maxi_mem (f : α → β) (h : s ≠ ∅) : s.maxi f ∈ s.image f :=
let ⟨a, ha⟩ := exists_mem_of_ne_empty h in
mem_of_max $ (iget_mem $ is_some_iff_exists.2 $ max_of_mem (mem_image_of_mem f ha))

lemma maxi_le {b : β} (hf : ∀a∈s, f a ≤ b) (hd : s = ∅ → default β ≤ b) : s.maxi f ≤ b :=
classical.by_cases
  (assume h : s = ∅, by simp * at * )
  (assume h : s ≠ ∅,
    let ⟨a, ha, eq⟩ := mem_image.1 $ maxi_mem f h in
    eq ▸ hf a ha)

lemma le_maxi {a : α} (h : a ∈ s) : f a ≤ s.maxi f :=
le_max_of_mem (mem_image_of_mem f h) (iget_mem $ is_some_iff_exists.2 $ max_of_mem (mem_image_of_mem f h))

lemma le_maxi_of_forall {b : β} (hb : ∀a∈s, b ≤ f a) (hd : s = ∅ → b ≤ default β) : b ≤ s.maxi f :=
classical.by_cases
  (assume h : s = ∅, by simp * at * )
  (assume h : s ≠ ∅,
    let ⟨a, ha, eq⟩ := mem_image.1 $ maxi_mem f h in
    eq ▸ hb a ha)

@[simp] lemma maxi_const {b : β} (h : s = ∅ → b = default β) : s.maxi (λa, b) = b :=
classical.by_cases
  (assume h : s = ∅, by simp * at * )
  (assume h, by simp [maxi, image_const h])

end Max

end finset

@[simp] lemma real.default_eq : default ℝ = 0 :=
rfl

namespace metric_space
open finset

instance fintype_function {α : β → Type*} [fintype β] [∀b, metric_space (α b)] :
  metric_space (Πb, α b) :=
{ dist := λf g, maxi univ (λb, _root_.dist (f b) (g b)),
  dist_self := assume f, by simp,
  dist_comm := assume f g, by congr; funext b; exact dist_comm _ _,
  dist_triangle := assume f g h, maxi_le
    (assume b hb,
      calc dist (f b) (h b) ≤ dist (f b) (g b) + dist (g b) (h b) : dist_triangle _ _ _
        ... ≤ maxi univ (λb, _root_.dist (f b) (g b)) + maxi univ (λb, _root_.dist (g b) (h b)) :
          add_le_add (le_maxi hb) (le_maxi hb))
    (by simp [le_refl] {contextual := tt}),
  eq_of_dist_eq_zero := assume f g eq0, funext $ assume b, dist_le_zero.1 $ eq0 ▸
    show dist (f b) (g b) ≤ maxi univ (λb, dist (f b) (g b)), from le_maxi (mem_univ b) }

#print axioms metric_space.fintype_function

end metric_space



#check (cardinal.{0})
#eval (∅ : finset ℕ).sup nat.succ

lemma h {α : Type*} (U : set α) : id '' U = U := by finish [set.image]
#print h

open nat int
lemma nat.mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n :=
by induction n; simp [*, nat.pow_succ, mul_comm, mul_assoc, mul_left_comm]

lemma nat.dvd_of_pow_dvd_pow : ∀ {a b n : ℕ}, 0 < n → a ^ n ∣ b ^ n → a ∣ b
| a 0     := λ n hn h, dvd_zero _
| a (b+1) := λ n hn h,
let d := nat.gcd a (b + 1) in
have hd : nat.gcd a (b + 1) = d := rfl,
  match d, hd with
  | 0 := λ hd, (eq_zero_of_gcd_eq_zero_right hd).symm ▸ dvd_zero _
  | 1 := λ hd,
    begin
      have h₁ : a ^ n = 1 := coprime.eq_one_of_dvd (coprime.pow n n hd) h,
      have := pow_dvd_pow a hn,
      rw [nat.pow_one, h₁] at this,
      exact dvd.trans this (one_dvd _),
    end
  | (d+2) := λ hd,
    have (b+1) / (d+2) < (b+1) := div_lt_self dec_trivial dec_trivial,
    have ha : a = (d+2) * (a / (d+2)) :=
      by rw [← hd, nat.mul_div_cancel' (gcd_dvd_left _ _)],
    have hb : (b+1) = (d+2) * ((b+1) / (d+2)) :=
      by rw [← hd, nat.mul_div_cancel' (gcd_dvd_right _ _)],
    have a / (d+2) ∣ (b+1) / (d+2) := nat.dvd_of_pow_dvd_pow hn $ dvd_of_mul_dvd_mul_left
      (show (d + 2) ^ n > 0, from pos_pow_of_pos _ (dec_trivial))
      (by rwa [← nat.mul_pow, ← nat.mul_pow, ← ha, ← hb]),
    by rw [ha, hb];
      exact mul_dvd_mul_left _ this
  end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf psigma.snd⟩]}

lemma int.nat_abs_pow (a : ℤ) (n : ℕ) : a.nat_abs ^ n = (a ^ n).nat_abs :=
by induction n; simp [*, nat.pow_succ, _root_.pow_succ, nat_abs_mul, mul_comm]

lemma int.dvd_of_pow_dvd_pow {a b : ℤ} {n : ℕ} (hn : 0 < n) (h : a ^ n ∣ b ^ n) : a ∣ b :=
begin
  rw [← nat_abs_dvd, ← dvd_nat_abs, ← int.nat_abs_pow, ← int.nat_abs_pow, int.coe_nat_dvd] at h,
  rw [← nat_abs_dvd, ← dvd_nat_abs, int.coe_nat_dvd],
  exact nat.dvd_of_pow_dvd_pow hn h
end

lemma int.cast_pow {α : Type*} [ring α] (a : ℤ) (n : ℕ) : ((a ^ n : ℤ) : α) = (a : α) ^ n :=
by induction n; simp [*, _root_.pow_succ]

def nth_root_irrational {x : ℤ} {a : ℚ} {n : ℕ} (hn : 0 < n) (h : a ^ n = x) : {a' : ℤ // a = a'} :=
have had : ((a.denom : ℤ) : ℚ) ≠ 0 := int.cast_ne_zero.2 (ne_of_lt (int.coe_nat_lt.2 a.3)).symm,
⟨a.num,
begin
  rw [rat.num_denom a, rat.mk_eq_div, div_pow _ had, div_eq_iff_mul_eq (pow_ne_zero _ had),
    ← int.cast_pow, ← int.cast_mul, ← int.cast_pow, int.cast_inj] at h,
  have := int.coe_nat_dvd.1 (dvd_nat_abs.2 (int.dvd_of_pow_dvd_pow hn (dvd_of_mul_left_eq _ h))),
  have := coprime.eq_one_of_dvd a.4.symm this,
  rw [rat.num_denom a, rat.mk_eq_div, this],
  simp,
end⟩

instance : euclidean_domain ℤ :=
{ quotient := (/),
  remainder := (%),
  quotient_mul_add_remainder_eq := λ a b,
    by rw [mul_comm, add_comm, int.mod_add_div],
  valuation := int.nat_abs,
  valuation_remainder_lt := λ a b hb, int.coe_nat_lt.1
    (by rw [← abs_eq_nat_abs b, nat_abs_of_nonneg (mod_nonneg _ hb)]; exact int.mod_lt a hb),
  le_valuation_mul := λ a b hb, by rw nat_abs_mul;
    exact le_mul_of_ge_one_right' (nat.zero_le _)
      (nat.pos_of_ne_zero (λ h, hb (eq_zero_of_nat_abs_eq_zero h))) }
#exit
def is_isom (G H : Σ α : Type*, group α) := nonempty (isom G H)

def lift_from {α β γ : Type*} (e : α ≃ β) (f : α → γ) (b : β) : γ := f (e.inv_fun b)

def lift_to {α β γ : Type*} (e : α ≃ β) (f : γ → α) (g : γ) : β := e (f g)

def lift_to_from {α β γ : Type*} (e : α ≃ β) (f : α → α) (b : β) : β := lift_from

class isom

def ring_of_ring_of_equiv (α β : Type*) [ring α] (e : α ≃ β) : ring β :=
{ mul := λ a b, e (e.inv_fun a * e.inv_fun b),
  mul_assoc := λ a b c, begin unfold_coes, rw [e.left_inv, e.left_inv, mul_assoc], end

}

theorem canonical_iso_is_canonical_hom {R : Type u} [comm_ring R] {f g : R} (H : Spec.D' g ⊆ Spec.D' f) :
let gbar := of_comm_ring R (powers f) g in
let sα : R → loc (away f) (powers gbar) :=
  of_comm_ring (away f) (powers gbar) ∘ of_comm_ring R (powers f) in
let sγ := (of_comm_ring R (non_zero_on_U (Spec.D' g))) in
by letI H2 := (canonical_iso H).is_ring_hom;
letI H3 : is_ring_hom sα := by apply_instance;
letI H4 : is_ring_hom sγ := by apply_instance; exact
@is_unique_R_alg_hom _ _ _ _ _ _ sγ sα (canonical_iso H).to_fun H4 H3 H2 :=

def disjoint {α β : Type*} [has_mem α β] (s t : β) := ∀ ⦃a : α⦄, a ∈ s → a ∈ t → false

def disjoint1 {α β : Type*} [has_mem α β] (s t : β) := ∀ ⦃a : α⦄, a ∈ s → a ∈ t → false
def add (n m : ℕ) : ℕ := nat.rec n (λ n, nat.succ) m

#eval add 34 3

example (X : Type) (R : Type) (D : R → set X) (γ : Type) (f : γ → R) :
  ⋃₀(D '' set.range f) = ⋃ (i : γ), D (f i) := set.ext (λ x, begin
rw set.sUnion_image, simp,
end)

theorem mk_eq : ∀ {a b c d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0),
  a /. b = c /. d ↔ a * d = c * b :=
suffices ∀ a b c d hb hd, mk_pnat a ⟨b, hb⟩ = mk_pnat c ⟨d, hd⟩ ↔ a * d = c * b,
[...]

example {p q t : ℕ+} {xp xq : ℤ} {m n : ℕ} (hm : (t : ℕ) = ↑p * m) (hn : (t : ℕ) = ↑q * n)
    (hpqt : xp * m = xq * n) : xp * q = xq * p :=
have hm0 : (m : ℤ) ≠ 0 := int.coe_nat_ne_zero.2 (λ h, lt_irrefl (0 : ℕ) (trans_rel_left
    (<) t.2 (by rwa [h, mul_zero] at hm))),
have hm' : (t : ℤ) = p * m := show ((t : ℕ) : ℤ) = p * m, from hm.symm ▸ by simp,
have hn' : (t : ℤ) = q * n := show ((t : ℕ) : ℤ) = q * n, from hn.symm ▸ by simp,
(domain.mul_right_inj hm0).1
  (by rw [mul_assoc xq, ← hm', hn', mul_left_comm, ← hpqt, mul_left_comm, mul_assoc])

inductive natε : Type
| ofnat : ℕ → natε
| addε : ℕ → natε

open natε

def add : natε → natε → natε
| (ofnat a) (ofnat b) := ofnat (a + b)
| (ofnat a) (addε b) := addε (a + b)
| (addε a) (ofnat b) := addε (a + b)
| (addε a) (addε b) := addε (a + b)



instance : has_add (natε) := ⟨add⟩

instance : add_comm_monoid natε :=
{ add := (+),
  zero := ofnat 0,
  add_assoc := λ a b c, by cases a; cases b; cases c; begin unfold has_add.add add,simp, end


}

example : α ≃ set α → false :=
λ f, function.cantor_surjective f f.bijective.2

lemma infinite_real : ¬ nonempty (fintype ℝ) := λ ⟨h⟩, set.infinite_univ_nat
(set.finite_of_finite_image
  (show function.injective (@nat.cast ℝ _ _ _), from λ x y, nat.cast_inj.1)
  ⟨@set_fintype ℝ h _ (classical.dec_pred _)⟩)

lemma omega_le_real : cardinal.omega ≤ ⟦ℝ⟧ :=
le_of_not_gt (λ h, infinite_real (cardinal.lt_omega_iff_fintype.1 h))

noncomputable def real_equiv_complex : ℝ ≃ ℂ :=
equiv.trans
  (classical.choice (quotient.exact (cardinal.mul_eq_self omega_le_real).symm))
  ⟨λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨_, _⟩, rfl, λ ⟨_, _⟩, rfl⟩
attribute [instance] classical.prop_decidable
theorem cantor_surjective (f : α → α → Prop) : ¬ function.surjective f | h :=
let ⟨D, e⟩ := h (λ a, ¬ f a a) in
(iff_not_self (f D D)).1 (iff_of_eq (congr_fun e D))

#print cantor_surjective
lemma em1 (p : Prop) : p ∨ ¬ p :=
have h : xor (xor true p) p :=
  begin
    unfold xor,
  end,

sorry⟩
#print eq.refl
def real_equiv_real_squared : ℝ ≃ (ℝ × ℝ) :=
{ to_fun :=


}

lemma red.trans {L₁ L₂ L₃ : list (α × bool)} (H12 : red L₁ L₂) (H23 : red L₂ L₃) : red L₁ L₃ :=
begin
  induction H23 with L1 L1 L2 L3 x b H ih generalizing L₁,
  case red.refl
  { assumption },
  case red.trans_bnot
  { exact red.trans_bnot (ih H12) }
end

lemma church_rosser {L₁ L₂ L₃ : list (α × bool)} (H12 : red L₁ L₂) (H13: red L₁ L₃) :
  ∃ L₄, red L₂ L₄ ∧ red L₃ L₄ :=
begin
  induction H12 with L1 L1 L2 L3 x1 b1 H1 ih1 generalizing L₃,
  case red.refl
  { exact ⟨L₃, H13, red.refl⟩ },
  case red.trans_bnot
  { specialize ih1 H13,
    rcases ih1 with ⟨L₄, H24, H34⟩,
    revert H24,
    generalize HL23 : L2 ++ (x1, b1) :: (x1, bnot b1) :: L3 = L23,
    intro H24,
    induction H24 with L4 L4 L5 L6 x2 b2 H2 ih2,
    case red.refl
    { subst HL23,
      exact ⟨_, red.refl, red.trans_bnot H34⟩ },
    case red.trans_bnot
    { subst HL23,
      admit } }
end

open equiv
variables {α : Type*}
#print not_iff
lemma mul_apply (a b : perm α) (x : α) : (a * b) x = (a (b x)) := rfl

@[simp] lemma one_apply (x : α) : (1 : perm α) x = x := rfl

def support (a : perm α) : set α := {x : α | a x ≠ x}
set_option pp.implicit true
set_option pp.notation false
example (a b n : ℕ) : (a * b)^n = a^n * b^n := begin have end

example (f g : perm α) : support (g * f * g⁻¹) = g '' support f :=
set.ext $ λ y, ⟨λ h : _ ≠ _, ⟨g⁻¹ y, λ h₁, by
  rw [mul_apply, mul_apply, h₁, ← mul_apply, mul_inv_self] at h;
  exact h rfl,
show (g * g⁻¹) y = y, by rw mul_inv_self; refl⟩,
λ ⟨x, (hx : _ ≠ _ ∧ _)⟩, show _ ≠ _,
begin
  rw [mul_apply, ← hx.2, ← mul_apply, ← mul_apply, mul_assoc, inv_mul_self, mul_one, mul_apply],
  assume h,
  rw (equiv.bijective g).1 h at hx,
  exact hx.1 rfl
end⟩

example (f g : perm α) : {x : X | conj g f x ≠ x} = {b : X | f (g⁻¹ b) ≠ g⁻¹ b}

universes u v l
variables {α : Type u} {β : Type v} {γ : Type*}
example (n : ℕ) (summand : ℕ → ℕ) : finset.sum finset.univ (λ (x : fin (succ n)), summand (x.val)) =
    summand n + finset.sum finset.univ (λ (x : fin n), summand (x.val)) := begin
  rw [← insert_erase (mem_univ (⟨n, lt_succ_self n⟩: fin (succ n))), sum_insert (not_mem_erase _ _)],
  refine congr_arg _ _,
  exact sum_bij (λ ⟨i, hi⟩ h, ⟨i, lt_of_le_of_ne (le_of_lt_succ hi) (fin.vne_of_ne (mem_erase.1 h).1)⟩) (λ _ _, mem_univ _)
  (λ ⟨_, _⟩ _, rfl) (λ ⟨a, _⟩ ⟨b, _⟩ _ _ (h : _), fin.eq_of_veq (show a = b, from fin.veq_of_eq h))
  (λ ⟨b, hb⟩ _, ⟨⟨b, lt_succ_of_lt hb⟩, ⟨mem_erase.2 ⟨fin.ne_of_vne (ne_of_lt hb), mem_univ _⟩, rfl⟩⟩)
end
#print num
example : (λ n : ℕ, 0) = (λ n, 0) := begin funext, end

example (n : ℕ) : (range n).sum (λ i, 2 * i + 1) = n * n :=
begin
  induction n with n hi,
  refl,
  rw [range_succ, sum_insert (λ h, lt_irrefl _ (mem_range.1 h)), hi, ← add_one],
  ring,
end

theorem meh {i : ℕ} {n : ℕ} : i < n → i < nat.succ n := λ H, lt.trans H $ nat.lt_succ_self _
#print sum_attach
theorem miracle (f : ℕ → ℕ)
(d : ℕ)
(Hd :
  ∀ (g : fin d → ℕ),
    (∀ (i : fin d), f (i.val) = g i) →
      finset.sum (finset.range d) f = finset.sum finset.univ g)
(g : fin (nat.succ d) → ℕ)
(h : ∀ (i : fin (nat.succ d)), f (i.val) = g i)
: finset.sum (finset.range d) f = finset.sum finset.univ (λ (i : fin d), g ⟨i.val, meh i.is_lt⟩)
:=
let gres : fin d → ℕ := λ (i : fin d), g ⟨i.val, meh i.is_lt⟩ in
by rw Hd gres (λ i, h ⟨i.val, _⟩)
#print miracle
example (n : ℕ) (f : ℕ → ℕ) (g : fin n → ℕ) (h : ∀ i : fin n, f i.1 = g i) :
    (range n).sum f = univ.sum g :=
sum_bij (λ i h, ⟨i, mem_range.1 h⟩) (λ _ _, mem_univ _) (λ a ha, h ⟨a, mem_range.1 ha⟩)
(λ _ _ _ _, fin.veq_of_eq) (λ ⟨b, hb⟩ _, ⟨b, mem_range.2 hb, rfl⟩)

lemma fin_sum (n : ℕ) (f : ℕ → ℕ) : (range n).sum f = univ.sum (f ∘ @fin.val n) :=
sum_bij (λ i h, fin.mk i (mem_range.1 h)) (λ _ _, mem_univ _) (λ _ _, rfl) (λ _ _ _ _, fin.veq_of_eq)
(λ ⟨b, hb⟩ _, ⟨b, mem_range.2 hb, rfl⟩)
#print fin_sum
#print fin_sum
#check multiset.pmap_eq_map
example (f : β → α) (g : γ → α) (s : finset γ)

lemma wilson (p : ℕ) (hp : prime p) : fact (p - 1) ≡ p - 1 [MOD p] :=
begin

end

inductive  ev : nat →  Prop
| ev_0 : ev 0
| ev_SS : ∀ n : nat, ev n → ev (n+2)
open ev

lemma ev_one : ¬ ev 1 := λ h, by cases h
#print ev_one
def double (n : ℕ) := n + n

lemma ev_double (n : ℕ) : ev (double n) :=
nat.rec ev_0 (λ n h, show ev (_ + _), from (succ_add (succ n) n).symm ▸ ev_SS _ h) n

example {α : Sort*} {f : perm α} : ∃ g h : perm α, g ∘ g = id ∧ h ∘ h = id ∧ f.1 = g ∘ h := begin


end

inductive P : ℕ → Prop
| intro (n : ℕ) : P n
#print ulift
inductive P1 (n : ℕ) : Prop
| intro : P1

#print P1.rec

#print P.rec

inductive eq2 : α → α → Prop
| refl : ∀ a, eq2 a a

#print eq2.rec
#print nat.div
inductive mystery : Sort u
| A : mystery
| B : mystery
#print mystery.rec
def f (n : ℕ) : P n → ℕ := @P.rec (λ n, ℕ) id n

def bla5d (n : ℕ) : ℕ := P.rec id (P.intro n)

lemma zero_one : P 0 = P 1 := propext ⟨λ _, P.intro 1, λ _, P.intro 0⟩

example : f 0 (P.intro 0) = f 1 (P.intro 1)

#print subtype
#check ℕ → ℤ
lemma succ_inj2 (n m : ℕ) : succ n = succ m → n = m :=
λ h, show natnc (succ n) = natnc (succ m), from eq.rec (eq.refl _) h

lemma succ_addax : ∀ b a : ℕ, succ a + b = succ (a + b) :=
λ a, nat.rec (λ a, eq.refl _) (λ a hi b,
show succ (succ b + a) = succ (succ (b + a)),
from eq.rec (eq.refl _) (hi b)) a

lemma zero_addax : ∀ a : ℕ, 0 + a = a :=
λ b, nat.rec (eq.refl zero)
(λ c (hc : 0 + c = c), show succ (0 + c) = succ c,
from @eq.rec _ _ (λ d, succ (0 + c) = succ d)
(show succ (0 + c) = succ (0 + c), from eq.refl _) _ hc) b

lemma add_commax : ∀ a b : ℕ, a + b = b + a := λ a,
nat.rec (λ b, zero_addax b)
(λ b hi c, show succ b + c = succ (c + b),
from eq.rec (eq.rec (succ_addax c b) (hi c)) (succ_addax c b)) a

#print nat.rec
inductive T : Prop
| mk : T → T
#print nat.strong_rec_on
lemma not_T : ¬T := λ h, T.rec_on h (λ _, id)
#print unit.rec

#print eq.rec
lemma f (n m : ℕ) : n = m → n = m :=
λ h, eq.rec rfl h
#print f
inductive T2
| mk : T2 → T2

example : T2 → false := λ t, T2.rec_on t (λ _, id)
inductive xnat
| zero : xnat
| succ : xnat → xnat

inductive prod2 (α β : Type*)
| mk (fst : α) (snd : β) : prod2

inductive prod3 (α β : Type*)
| mk (fst : α) (snd : β) : prod3

def prod2.fst (α β : Type*) (x : prod2 α β) : α :=
prod2.rec (λ a _, a) x
#print sum

inductive pint
| one : pint
| d : pint → pint
| da : pint → pint

inductive xnat1
| succ : xnat1 → xnat1
| zero : xnat1
| blah : xnat1 → xnat1

#print xnat1.rec
open pint
#print pint.rec_on

def padd_one : pint → pint
| one    := d one
| (d m)  := da m
| (da m) := d (padd_one m)

def padd : pint → pint → pint
| one m         := padd_one m
| n one         := padd_one n
| (d n) (d m)   := d (padd n m)
| (d n) (da m)  := da (padd n m)
| (da n) (d m)  := da (padd n m)
| (da n) (da m) := d (padd_one (padd n m))

inductive rel : pint → pint → Prop
| oned : ∀ n : pint, rel one (d n)
| oneda : ∀ n : pint, rel one (da n)

def pintwf : has_well_founded Σ' pint, pint :=
{ r := rel,
  wf := well_founded.intro sorry
}

lemma sizeof_pos : ∀ n : pint, 0 < pint.sizeof n
| one    := dec_trivial
| (d m)  := by unfold pint.sizeof; rw add_comm; exact succ_pos _
| (da m) := by unfold pint.sizeof; rw add_comm; exact succ_pos _

def padd2 : pint → pint → pint
| one one       := d one
| one (d m)     := da m
| one (da m)    := d (padd2 one m)
| (d n) one     := da n
| (d n) (d m)   := d (padd2 n m)
| (d n) (da m)  := da (padd2 n m)
| (da n) one    := d (padd2 n one)
| (da n) (d m)  := da (padd2 n m)
| (da n) (da m) := have h : 0 < pint.sizeof n, from sizeof_pos _,
    d (padd2 one (padd2 n m))

#print nat.below
inductive eq2 (a : ℕ) : ℤ → Prop
| refl : eq2 2

inductive eq3 : Π {α : Sort u}, α → α → Prop
| refl : ∀ {α : Sort u} (a : α), eq3 a a

inductive bla3 (a : ℕ) : ℤ → Prop
| one : ∀ i : ℤ, bla3 (i + a)
| two : bla3 2
| three : ∀ i : ℤ, i < a → bla3 i

inductive bla4 (a : ℕ) : ℕ → Type
| one : Π n : ℕ, bla4 (a + n)

inductive bla5 : ℕ → Prop
| intro (n : ℕ) : bla5 n
#print bla5.rec

def fb (n : ℕ) : bla5 n → ℕ := @bla5.rec (λ n, ℕ) id n

def bla5d (n : ℕ) : ℕ := bla5.rec id (bla5.intro n)
#eval bla5d 5
#reduce bla5d 5
lemma zero_one : bla5 0 = bla5 1 := propext ⟨λ _, bla5.intro 1, λ _, bla5.intro 0⟩

example : @bla5.rec (λ n, ℕ) id (bla5.intro 0) : ℕ) = bla5.rec id (bla5.intro 1) :=
@eq.drec_on Prop (bla5 1) (λ a b, begin end) (bla5 2) zero_one rfl


axiom bla4.rec2 : ∀ {a : ℕ} {C : ℕ → Sort l}, (∀ (n : ℕ), C (a + n)) →
    ∀ {b : ℕ}, bla4 a b → C b
#print bla4.rec
axiom bla4_iota {a : ℕ} {C : ℕ → Sort l} (f : Π n, C (a + n)) {b : ℕ}
 : @bla4.rec a C f b (bla4.one b) =

#print bla4.rec
#print acc.rec
#print eq
#print eq3
#print eq.rec
#print bla3.rec
#print list.perm.rec
#print psum.rec

lemma bla3.rec2 {a : ℕ} {C : ℤ → Sort l} : (Π i : ℤ, C (i + a)) → C 2 →
(Π i : ℤ, i < a → C i) → Π i : ℤ, bla3 a i → C i := @bla3.rec a C

#print eq2.rec

universe l
#print nat.no_confusion_type
#print nat.no_confusion
#print nat.succ.inj

#print int.cases_on
#print int.rec_on

lemma no_confusion1 : Π {P : Sort l} {v1 v2 : ℕ}, v1 = v2 → nat.no_confusion_type P v1 v2 :=
assume P v1 v2 h,begin
  rw h,
  induction v2,
  exact id,
  assume h,
  exact h rfl,
end

lemma preod {α β : Type*} (p : α × β) : p = prod.mk p.fst p.snd :=
prod.rec (λ f s, rfl) p
#print sigma.rec
lemma bla (P Q R : Prop) : (P ∧ Q → R) ↔ (P → (Q → R)) :=
iff.intro (λ h hp hq, h (and.intro hp hq)) (λ h hpq, h (and.left hpq) (and.right hpq))
#print bla

lemma succ_inj {n m : ℕ} : nat.succ m = nat.succ n → m = n :=
λ h, nat.no_confusion h id

lemma succ_ne_zero (n : ℕ) : nat.succ n ≠ nat.zero :=
@nat.no_confusion _ (nat.succ n) nat.zero

lemma succ_ne (n : ℕ) : nat.succ n ≠ n :=
nat.rec (succ_ne_zero nat.zero) (λ n h hi, h $ succ_inj hi) n
#print prod
def bool.no_confusion_type1 : Sort l → bool → bool → Sort l :=
λ P v1 v2, bool.rec (bool.rec (P → P) P v2)
(bool.rec P (P → P) v2) v1

lemma prod.mk_inj {α : Type u} {β : Type v} {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β}
  : (x₁, y₁) = (x₂, y₂) → and (x₁ = x₂) (y₁ = y₂) :=
λ h, ⟨show (x₁, y₁).fst = (x₂, y₂).fst, from eq.rec (eq.refl _) h,
      show (x₁, y₁).snd = (x₂, y₂).snd, from eq.rec (eq.refl _) h⟩
set_option pp.implicit true

example : @bool.no_confusion_type1 = @bool.no_confusion_type := rfl
def f : xnat → bool := λ n, xnat.rec ff (λ n h, bnot h) n

lemma bool.no_confusion1 {v1 v2 : bool} : v1 = v2 → bool.no_confusion_type1 false v1 v2 :=
λ h, eq.rec (bool.rec id id v1) h

example : tt ≠ ff := bool.no_confusion1

example (n : xnat) : succ n ≠ n := xnat.rec n begin end sorry

axiom em2 (p : Prop) : p ∨ ¬p

lemma choice2 {α : Sort*} : nonempty (nonempty α → α) :=
begin
  have := em2 (nonempty α),
  cases this,
  cases this,
  exact ⟨λ h, this⟩,
  exact ⟨λ h, false.elim (this h)⟩
end

inductive acc2 {α : Sort u} (r : α → α → Prop) : α → Prop
| intro (x : α) (h : ∀ y, r y x → acc2 y) : acc2 x
#print prefix acc2
axiom em3 (p : Prop) : decidable p
