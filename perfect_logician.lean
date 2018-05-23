import data.nat.basic
open nat
def island_rules : ℕ → ℕ → (ℕ → Prop)
| 0        b :=  λ bb, (bb = b ∨ bb = b - 1) ∧ bb > 0
| (succ d) b := (λ bb, (island_rules d b) bb ∧ 
                ((∀ c, (island_rules d b) c → c = b) ↔ (∀ c, (island_rules d bb) c → c = bb)))
theorem init_island {d b bb} : (island_rules d b) bb → (bb = b ∨ bb = b - 1) ∧ bb > 0 := begin
    induction d with d hi,unfold island_rules,assume h,exact h,
    unfold island_rules,assume h,exact hi h.left
end
theorem blue_eyed_islander : ∀ d b : ℕ, b > 0 → (d + 1 ≥ b ↔ (∀ bb:ℕ, (island_rules d b) bb → bb = b)):=begin
    assume d,induction d with d hi,assume b,
    simp[island_rules],
    cases b,simp[(dec_trivial:¬0>0)],
    cases b,assume h,simp[(dec_trivial:1≥1)],assume bb hbb,cases hbb,assume hbb1,rw hbb,
    rw hbb,simp[(dec_trivial:¬0>0)],
    assume h,simp[(dec_trivial:¬ 1 ≥ succ (succ b))],assume hbb,
    have h1:=hbb (succ b),simp[(dec_trivial:succ b>0),succ_ne_self (succ b)] at h1,
    exact (succ_ne_self b).symm h1,

    assume b hb,apply iff.intro,
    assume hd,cases lt_or_eq_of_le hd,unfold island_rules,assume bb hbb,
    have hd1 : succ d ≥ b:=le_of_succ_le_succ (succ_le_of_lt h),rw add_one at hi,
    exact iff.elim_left (hi b hb) hd1 bb hbb.left,

    have hi1:= hi b hb,rw succ_add at h,rw h at hi1,
    have hd1:¬d+1 ≥ succ(d+1) :=not_le_of_gt (lt_succ_self (d+1)),
    simp[hd1] at hi1,unfold island_rules,assume bb hbb,
    have hbb1:=init_island hbb.left,
    cases hbb1.left with hbb2 hbb2,assumption,
    have hbbd:d + 1 ≥ bb,rw[eq_comm,nat.sub_eq_iff_eq_add (succ_le_of_lt hb)] at hbb2,
    rw [hbb2,succ_add,add_one bb] at hd,exact le_of_succ_le_succ hd,
    exact iff.elim_right hbb.right (iff.elim_left (hi bb hbb1.right) hbbd) bb hbb.left,

    assume hbb,apply by_contradiction,assume hd,have hd1:=lt_of_not_ge hd,
    rw succ_add at hd1,have hd2:¬d + 1 ≥ b:=not_le_of_gt (lt_of_succ_lt hd1),
    have hi1:= hi b hb,simp [hd2] at hi1,unfold island_rules at hbb,
    rw classical.not_forall at hi1,cases hi1 with bb hbb1,
    rw @not_imp _ _ (classical.prop_decidable _)at hbb1,
    have hbb2:=hbb bb,
    have hbb3:= init_island hbb1.left,simp[hbb1.right] at hbb3,
    have hbb4:=hi bb hbb3.right,
    rw [eq_comm,nat.sub_eq_iff_eq_add (succ_le_of_lt hb)] at hbb3,
    rw [hbb3.left,add_one bb] at hd1,have hbbd:¬d + 1 ≥ bb:= not_le_of_gt (lt_of_succ_lt_succ hd1),
    simp[hbbd] at hbb4,
    have:¬∀ (c : ℕ), island_rules d b c → c = b,assume hbb4,have:=hbb4 bb hbb1.left,
    rw [hbb3.left,add_one,eq_comm] at this,exact succ_ne_self bb this,
    simp[hbb4,hbb1.left,this] at hbb2,
    rw [hbb3.left,add_one,eq_comm] at hbb2,exact succ_ne_self bb hbb2,    
end
#print blue_eyed_islander