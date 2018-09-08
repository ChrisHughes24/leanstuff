import data.nat.prime data.finset
open nat

def island_rules : ℕ → ℕ → ℕ → Prop
| 0       b B := (B = b ∨ B = b - 1) ∧ B > 0
| (d + 1) b B := island_rules d b B ∧
 ((∀ C, island_rules d b C → C = b) ↔ ∀ C, island_rules d B C → C = B)

def island_rules2 : ℕ → ℕ → finset ℕ
| 0     b := ({b - 1, b} : finset ℕ).filter (> 0)
| (d+1) b := (island_rules2 d b).filter
  (λ B, (∀ C ∈ island_rules2 d b, C = b) ↔ (∀ C ∈ island_rules2 d B, C = B))

lemma island_rules_iff (d : ℕ) : ∀ b B, island_rules d b B ↔ B ∈ island_rules2 d b :=
by induction d; simp [island_rules, island_rules2, *]; tauto

lemma island_rules_iff' (d : ℕ) : ∀ b, (∀ B, island_rules d b B → B = b) ↔ (∀ B ∈ island_rules2 d b, B = b) :=
by simp [island_rules_iff]

instance decg : decidable_rel (λ d b, ∀ B, island_rules d b B → B = b) :=
λ d b, decidable_of_iff _ (island_rules_iff' d b).symm

lemma blue_eyed_islander : ∀ d < 100, (∀ B, island_rules d 100 B → B = 100) ↔ d = 99 := dec_trivial

#print axioms blue_eyed_islander
#exit
theorem blue_eyed_islander : ∀ d b, b > 0 → d + 1 ≥ b → ∀ B, island_rules d b B → B = b := λ d,
 nat.rec_on d (λ b, nat.cases_on b (λ h, absurd h (dec_trivial : ¬0 > 0)) (λ b, nat.cases_on b
 (λ h h B hB, or.by_cases hB.left (λ h1, h1) (λ h1, false.elim ((dec_trivial : ¬1 - 1 > 0) (h1 ▸
 hB.right)))) (λ b h h2, absurd h2 (dec_trivial : ¬0 + 1 ≥ succ (succ b))))) (λ d hi b hb hd B hB,
 have h_i : (B = b ∨ B = b - 1) ∧ B > 0 := nat.rec_on d (λ h, h) (λ d hi h, hi h.left) hB.left,
 or.by_cases h_i.left (λ h, h) (λ h, hB.right.mpr (hi B h_i.right (le_of_succ_le_succ (((
 (nat.sub_eq_iff_eq_add (succ_le_of_lt hb)).mp h.symm) ▸ hd) : d + 2 ≥ B + 1))) B hB.left))

theorem init_island {d b B} : island_rules d b B → (B = b ∨ B = b - 1) ∧ B > 0 :=
 nat.rec_on d (λ h, h) (λ d hi h, hi h.left)

theorem blue_eyed_islander1 : ∀ d b, b > 0 → (d + 1 ≥ b ↔ ∀ B, island_rules d b B → B = b) :=
 λ d, nat.rec_on d (λ b, nat.cases_on b (λ h, absurd h (dec_trivial : ¬0 > 0)) $ λ b, nat.cases_on
 b (λ h, ⟨λ h B hB, or.by_cases hB.left (λ h1, h1) (λ h1, false.elim $ (dec_trivial : ¬1 - 1 > 0) $
 h1 ▸ hB.right), λ h, dec_trivial⟩) $ λ b h, ⟨λ h2, false.elim ((dec_trivial : ¬0 + 1 ≥ succ (succ
 b)) h2), λ hB, false.elim $ (succ_ne_self $ succ b).symm $ hB (succ b) ⟨or.inr (succ_sub_one $
 succ b).symm, dec_trivial⟩⟩) $ λ d hi b hb, ⟨λ hd, or.by_cases (lt_or_eq_of_le hd) (λ h B hB, (hi
 b hb).mp (le_of_succ_le_succ $ succ_le_of_lt h) B hB.left) $ λ h B hB, or.by_cases (init_island
 hB.left).left (λ h, h) $ λ h, hB.right.mpr ((hi B (init_island hB.left).right).mp $
 le_of_succ_le_succ $ (((nat.sub_eq_iff_eq_add $ succ_le_of_lt hb).mp h.symm).trans $ add_one B) ▸
 hd) B hB.left, λ hB, by_contradiction $ begin
   rw island_rules2_iff_island_rules at hB,
 end

#print axioms blue_eyed_islander1
