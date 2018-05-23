import data.nat.prime
import tactic.norm_num
import data.list.basic
import data.int.basic
open nat
open list

theorem  prime_factors_unique: ∀ A B:list ℕ,prod A=prod B→(∀p:ℕ, p∈A→prime p)→(∀ p:ℕ,p∈ B→ prime p)→A~B:=begin
    intro A,induction A with pA A1 Hi,
    norm_num,intros,cases B with p B1,exact perm.refl nil,exfalso,revert a,norm_num,
    have H:=a_1 p (list.mem_cons_self _ _),have H1:=dvd_mul_right p (prod B1),intro,rw ←a at H1,exact prime.not_dvd_one H H1,
    intros,simp at a,have H:pA ∣ prod B, have:=dvd_mul_right pA (prod A1),rwa a at this,
    have H1: ∀ (B:list ℕ)(p:ℕ),prime p→(∀pB, pB ∈ B → prime pB)→p ∣ prod B → p ∈ B:=begin
        assume B,induction B with p1 B1 Hi,
        rw prod_nil,assume p Hp H H2,exfalso,revert H2,
        exact prime.not_dvd_one Hp,
        assume p2 Hp2 H H1,
        norm_num,rw prod_cons at H1,
        have H2:=iff.elim_left (prime.dvd_mul Hp2) H1,
        cases H2 with A A,left,
        have H3:=H p1,
        revert H3,norm_num,assume H4,
        unfold prime at H4,
        have H5:=and.right H4 p2 A,
        have H6:¬p2=1:=begin unfold prime at Hp2,intro,rw a_3 at Hp2,simp at Hp2,revert Hp2,exact dec_trivial,end,
        simp [H6] at H5,assumption,right,
        have H3:(∀ (pB : ℕ), pB ∈ B1 → prime pB):=begin revert H, norm_num,end,have H2:= Hi p2 Hp2 H3 A,assumption,
    end,
    have HppA: prime pA:=begin apply a_1,norm_num,  end,
    have H9:=H1 B pA HppA a_2 H,
    have H11:=prod_eq_of_perm (perm_erase H9),rw [H11,prod_cons] at a,
    rw nat.mul_left_inj (gt_of_ge_of_gt (and.left HppA) (dec_trivial:2>0)) at a,
    have HA1:∀ (p : ℕ), p ∈ A1 → prime p:=begin revert a_1,norm_num,end,
    have HB1:∀ (p : ℕ), p ∈(list.erase B pA) → prime p:=λ p Hp,a_2 p (mem_of_mem_erase Hp),
    have Hi2:= iff.elim_right (perm_cons pA) (Hi (list.erase B pA) a HA1 HB1),
    exact perm.trans Hi2 (perm.symm (perm_erase H9)),
end
