import data.finset tactic.find data.fintype data.nat.basic data.pnat
universes u v
local infix ` ≺ ` :50 := has_well_founded.r

open well_founded
#print array
lemma acc.rec_3 {α : Sort u} [hw : has_well_founded α] {C : α → Sort v}
  (f : Π x, (∀ y, y ≺ x → acc (≺) y) → (Π y, y ≺ x → C y) → C x) (a : α) :
  @acc.rec α (≺) C f a (apply hw.wf a) = f a (λ y _, apply hw.wf y) 
  (λ y hya, @acc.rec α (≺) C f y (apply hw.wf y)) := 
(show acc.intro a (λ y _, apply hw.wf y) = (apply hw.wf a), from rfl) ▸ rfl

class game (α : Type*) extends has_well_founded α :=
(start_position : α)
(side_to_move : α → bool)
(legal_moves : Π a, finset {b : α // b ≺ a ∧ side_to_move b = bnot (side_to_move a)})
(max_score : ℕ)
(not_boring : max_score > 1)
(final_score : Π {a}, legal_moves a = ∅ → fin max_score)

namespace game

open well_founded finset list
variables {α : Type*} [g : game α] [decidable_eq α]
include g

def is_legal_move (a b : α) := ∃ h : b ≺ a ∧ side_to_move b = bnot (side_to_move a), 
(⟨b, h⟩ : {b : α // b ≺ a ∧ side_to_move b = bnot (side_to_move a)}) ∈ legal_moves a

lemma is_legal_move_of_mem {a : α} {b : {b : α // b ≺ a ∧ _}} : b ∈ legal_moves a → is_legal_move a b :=
let ⟨b1, b2⟩ := b in λ h, ⟨b2, h⟩

lemma max_score_pos : 0 < max_score α :=
nat.pos_of_ne_zero $ λ h0, 
acc.rec_on (apply g.wf (start_position α)) $ λ a h₁ h₂, or.by_cases
(decidable.em (legal_moves a = ∅)) 
(λ h, (not_lt_of_ge (nat.zero_le _)) (show (final_score h).val < 0, from h0 ▸ (final_score h).2)) $
λ h, let ⟨⟨y, hy₁⟩, hy⟩ := exists_mem_of_ne_empty h in h₂ y hy₁.1

def best (s : bool) (sc₁ sc₂ : fin g.max_score) : fin g.max_score :=
bool.cases_on s ⟨min sc₁.1 sc₂.1, lt_of_le_of_lt (min_le_left _ _) sc₁.2⟩ 
⟨max sc₁.1 sc₂.1, max_lt sc₁.2 sc₂.2⟩

def better (s : bool) (sc₁ sc₂ : fin g.max_score) : Prop :=
bool.cases_on s (sc₁.1 ≤ sc₂.1) (sc₂.1 ≤ sc₁.1)

@[refl] lemma better.refl (s : bool) (sc : fin g.max_score) : better s sc sc :=
bool.cases_on s (le_refl _) (le_refl _)

lemma better.trans {s : bool} {sc₁ sc₂ sc₃ : fin g.max_score} : better s sc₁ sc₂ → 
    better s sc₂ sc₃ → better s sc₁ sc₃ :=
bool.cases_on s le_trans (λ h₁ h₂, le_trans h₂ h₁)

lemma best_better (s : bool) (sc₁ sc₂ : fin g.max_score) : better s (best s sc₁ sc₂) sc₁:=
bool.cases_on s (min_le_left _ _) (le_max_left _ _)

lemma better_swap {s : bool} {sc₁ sc₂ : fin g.max_score} : better (bnot s) sc₁ sc₂ ↔ better s sc₂ sc₁ :=
bool.cases_on s iff.rfl iff.rfl

def worst (s : bool) (sc₁ : fin g.max_score) (sc₂ : fin g.max_score) := best (bnot s) sc₁ sc₂

def win (s : bool) : fin g.max_score := bool.cases_on s 
⟨0, max_score_pos⟩ ⟨nat.pred g.max_score, nat.pred_lt (ne_of_lt max_score_pos).symm⟩

lemma win_better (s : bool) (sc : fin g.max_score) : better s (win s) sc :=
bool.cases_on s (nat.zero_le _) (nat.le_of_succ_le_succ $
show nat.succ sc.1 ≤ nat.succ (nat.pred (max_score α)),
  begin rw nat.succ_pred_eq_of_pos max_score_pos, exact sc.2, end)

lemma eq_win_of_better_win {s : bool} {sc : fin g.max_score} : better s sc (win s) → sc = win s :=
bool.cases_on s (λ h, fin.eq_of_veq $ le_antisymm h (win_better ff _))
(λ h, fin.eq_of_veq $ le_antisymm (win_better tt _) h)

def loss (s : bool) := @win α _ (bnot s)

lemma eq_loss_of_loss_better {s : bool} {sc : fin g.max_score} : better s (loss s) sc → 
    sc = loss s :=
bool.cases_on s (λ h, fin.eq_of_veq $ (le_antisymm (win_better tt _) h))
(λ h, fin.eq_of_veq $ le_antisymm h (win_better ff _))

instance (s : bool) : is_commutative _ (@best α _ s) := ⟨λ ⟨a, _⟩ ⟨b, _⟩, fin.eq_of_veq $
bool.cases_on s (min_comm _ _) (max_comm _ _)⟩ 

instance (s : bool) : is_associative _ (@best α _ s) := ⟨λ ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, 
fin.eq_of_veq $ bool.cases_on s (min_assoc a b c) (max_assoc a b c)⟩

def score (a : α) : fin g.max_score := 
acc.rec_on (apply g.wf a) $ λ a _ score,
if h : legal_moves a = ∅
then final_score h
else fold (best (side_to_move a))
  (loss (side_to_move a))
  (λ b : {b : α // b ≺ a ∧ side_to_move b = bnot (side_to_move a)}, score b.1 b.2.1)
  (legal_moves a)

lemma score_eq (a : α) : score a = dite (legal_moves a = ∅) (λ h, final_score h)
    (λ h, multiset.fold (best (side_to_move a)) (loss (side_to_move a))
    (multiset.map (λ b : {b : α // _}, score b.1) ((legal_moves a).1))) :=
by unfold score fold; rw acc.rec_3

lemma score_better_aux {a : fin g.max_score} {s : multiset (fin g.max_score)} (b : bool) : 
    a ∈ s → better b (multiset.fold (best b) (loss b) s) a :=
multiset.induction_on s (λ h, absurd h (multiset.not_mem_zero _)) $ λ n s hi h,
or.by_cases (multiset.mem_cons.1 h) (λ h₁, by rw [multiset.fold_cons_left, h₁];
exact best_better _ _ _) (λ h₁, by rw [multiset.fold_cons_right];
exact better.trans (best_better _ _ _) (hi h₁))

lemma score_better {a b : α} (h : is_legal_move a b) : better (side_to_move a) (score a) (score b) :=
let ⟨hb₁, hb₂⟩ := h in
by rw [score_eq a, dif_neg (ne_empty_of_mem hb₂)];
  exact score_better_aux _ (multiset.mem_map.2 ⟨⟨b, hb₁⟩, hb₂, rfl⟩)

lemma win_of_winning_move {a b : α} : score b = win (side_to_move a) →
    is_legal_move a b → score a = win (side_to_move a) :=
λ h₁ h₂, eq_win_of_better_win (h₁ ▸ score_better h₂)

lemma losing_move_of_loss {a b : α} :  is_legal_move a b → score a = loss (side_to_move a) →
    score b = loss (side_to_move a) := 
λ h₁ h₂, eq_loss_of_loss_better (h₂ ▸ (score_better h₁))

lemma win_ne_loss (s : bool) : @win α _ s ≠ loss s :=
bool.cases_on s (fin.ne_of_vne $ ne_of_lt $ nat.lt_pred_of_succ_lt $ not_boring α)
(fin.ne_of_vne (ne_of_lt $ nat.lt_pred_of_succ_lt $ not_boring α).symm)

end game
open game well_founded fintype list finset
def nim := ℕ × bool
#print forall_eq
instance : game nim :=
{ to_has_well_founded := ⟨_, measure_wf prod.fst⟩,
  start_position := ⟨21, tt⟩,
  side_to_move   := prod.snd,
  legal_moves    := λ n, if h : n.1 > 0 
    then {⟨⟨n.1 - 1, bnot n.2⟩, ⟨nat.sub_lt h dec_trivial, rfl⟩⟩,
          ⟨⟨n.1 - 2, bnot n.2⟩, ⟨nat.sub_lt h dec_trivial, rfl⟩⟩,
          ⟨⟨n.1 - 3, bnot n.2⟩, ⟨nat.sub_lt h dec_trivial, rfl⟩⟩}
    else ∅,
  max_score := 2,
  not_boring := dec_trivial,
  final_score := λ a h, if a.snd = ff then ⟨1, dec_trivial⟩
      else ⟨0, dec_trivial⟩ }

namespace nim

lemma hgf : score (start_position nim) = ⟨1, dec_trivial⟩ := rfl

lemma legal_moves_eq_empty_iff (n : nim) : legal_moves n = ∅ ↔ n.1 = 0 :=
⟨λ (h : dite (n.1 > 0)
    (λ h, ({⟨⟨n.1 - 1, bnot n.2⟩, ⟨nat.sub_lt h dec_trivial, rfl⟩⟩,
            ⟨⟨n.1 - 2, bnot n.2⟩, ⟨nat.sub_lt h dec_trivial, rfl⟩⟩,
            ⟨⟨n.1 - 3, bnot n.2⟩, ⟨nat.sub_lt h dec_trivial, rfl⟩⟩}
            : finset {b : nim //b ≺ n ∧ side_to_move b = bnot (side_to_move n)}))
    (λ h, ∅) = ∅), by_contradiction $ λ h₁,  
by simpa [dif_pos (nat.pos_of_ne_zero h₁)] using h,
λ h, or.by_cases (decidable.em (n.2 = tt)) 
(λ h₁, by rw (show n = ⟨0, tt⟩, from prod.eq_iff_fst_eq_snd_eq.2 ⟨h, h₁⟩); refl)
(λ h₁, by rw (show n = ⟨0, ff⟩, from prod.eq_iff_fst_eq_snd_eq.2 
  ⟨h, (iff_of_eq $ eq_ff_eq_not_eq_tt n.2).1 h₁⟩); refl)⟩

lemma mod_4 (n : ℕ) : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3

lemma score_nim (n : nim) : score n = loss (side_to_move n) ↔ 4 ∣ n.1 :=
acc.rec_on (apply nim.game.wf n) $ λ n ht hi, 
⟨λ h, or.by_cases (decidable.em (legal_moves n = ∅))
  (λ h₁, by rw legal_moves_eq_empty_iff at h₁; rw h₁; exact dec_trivial)
  (λ h₁, let ⟨y, hy⟩ := exists_mem_of_ne_empty h₁ in 
  begin 
    have := (hi y.1 y.2.1),
    unfold side_to_move at this,
    have h₂ : y.1.2 = bnot (side_to_move n) := y.2.2,
    have h₃ : score y.1 = loss (side_to_move n) := losing_move_of_loss (is_legal_move_of_mem hy) h,
    rw [h₂, loss, bnot_bnot, h₃, eq_comm] at this,
    simp [win_ne_loss] at this,
    have : y.1.1 > 0 := nat.pos_of_ne_zero (λ h, by rw h at this; exact absurd this dec_trivial),
    
    
  end)
, sorry⟩  

end nim

def nac := {l : list (fin 9) // nodup l}

lemma list_fin_length (n : ℕ) (l : {l : list (fin n) // nodup l}) : length l.1 ≤ n :=
begin
  suffices : length (l.1) ≤ fintype.card (fin n),
    rwa fintype.card_fin at this,
  rw [← multiset.coe_card, ← finset.card_def ⟨(↑l.1 : multiset (fin n)), multiset.coe_nodup.1 l.2⟩],
  exact card_le_of_subset (subset_univ _),
end

local notation `O`  := (⟨0, dec_trivial⟩ : fin 3)
local notation `X`  := (⟨1, dec_trivial⟩ : fin 3)
local notation `E`  := (⟨2, dec_trivial⟩ : fin 3)
local notation `pX` := tt
local notation `pO` := ff

instance : has_well_founded nac :=
⟨_, measure_wf (λ p, 9 - length p.1)⟩

def legal_moves' (p : list (fin 9)) : finset (fin 9) := 
list.rec_on p univ (λ n p lp, (finset.erase lp n))

lemma legal_moves'_not_mem : ∀ {p : list (fin 9)} {n : fin 9}, n ∈ legal_moves' p → n ∉ p 
| nil      n h := not_mem_nil _
| (m :: p) n h := not_mem_cons_of_ne_of_not_mem (ne_of_mem_erase h) $
legal_moves'_not_mem (finset.mem_of_mem_erase h)

def legal_moves1 (p : nac) : finset {q : nac // q ≺ p} := 
⟨multiset.pmap (λ n h, ⟨⟨list.cons n p.1, nodup_cons_of_nodup h p.2⟩,
(nat.sub_lt_sub_left_iff (list_fin_length 9 ⟨n :: p.1, nodup_cons_of_nodup h p.2⟩)).2 
(nat.lt_succ_self _)⟩) (legal_moves' p.1).1 (λ n h, legal_moves'_not_mem h),
multiset.nodup_pmap (by intros; simp * at *) (legal_moves' p.1).2⟩ 

def is_line (p : nac) : 

instance : game nac := 
{ start_position := ⟨nil, nodup_nil⟩,
  legal_moves    := }


end game