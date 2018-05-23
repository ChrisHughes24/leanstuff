import data.nat.modeq data.nat.basic data.nat.prime data.int.basic tactic.norm_num tactic.ring
def int.prime : ℤ → Prop := λ x,nat.prime (int.nat_abs x)

theorem prime_dvd_mul {p m n : ℤ} (pp : int.prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=begin
    have H:int.nat_abs p ∣int.nat_abs m * int.nat_abs n ↔ int.nat_abs p ∣ int.nat_abs m ∨ int.nat_abs p ∣int.nat_abs n:=begin
        unfold int.prime at pp,revert pp, exact nat.prime.dvd_mul,end,
    rw [←int.coe_nat_dvd,←int.coe_nat_dvd,←int.coe_nat_dvd,int.coe_nat_mul,int.nat_abs_dvd,int.nat_abs_dvd,int.nat_abs_dvd,
    ←int.abs_eq_nat_abs,←int.abs_eq_nat_abs] at H,cases lt_trichotomy m 0 with Hm Hm,
    cases lt_trichotomy n 0 with Hn Hn,rwa[abs_of_neg Hm,abs_of_neg Hn,dvd_neg,dvd_neg,neg_mul_neg] at H,
    cases Hn with Hn Hn,rw Hn,norm_num,rwa[abs_of_neg Hm,abs_of_pos Hn,dvd_neg,←neg_mul_eq_neg_mul,dvd_neg] at H,
    cases Hm with Hm Hm,rw Hm,simp,cases lt_trichotomy n 0 with Hn Hn,rwa[abs_of_neg Hn,abs_of_pos Hm,dvd_neg,mul_neg_eq_neg_mul_symm,dvd_neg] at H,
    cases Hn with Hn Hn,rw Hn,simp,rwa[abs_of_pos Hn,abs_of_pos Hm] at H,
end
theorem dioph_identity:∀ a b p q:ℤ, (a*a+b*b)*(p*p+q*q)=(a*p+b*q)*(a*p+b*q)+(a*q-b*p)*(a*q-b*p):=begin
    intros,rw[mul_add,mul_add,add_mul,add_mul,add_mul,add_mul,mul_sub,sub_mul,sub_mul],ring,
end
theorem lemma_1 : ∀ a b p q : ℤ,∃ x y:ℤ, x*x+y*y=(a*a+b*b)*(p*p+q*q):=begin
    intros,existsi [(a*p+b*q),(a*q-b*p)],simp[mul_add,add_mul],ring
end
theorem lemma_1_nat :∀ a b p q : ℕ,∃ x y:ℕ, x*x+y*y=(a*a+b*b)*(p*p+q*q):=begin
    assume a b p q,cases lemma_1 ↑a ↑b ↑p ↑q with x hxy,cases hxy with y,existsi [int.nat_abs x,int.nat_abs y],
    rw[←int.coe_nat_eq_coe_nat_iff,int.coe_nat_add,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_add,int.coe_nat_add,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_mul],
    rwa[←int.abs_eq_nat_abs,←int.abs_eq_nat_abs,abs_mul_abs_self,abs_mul_abs_self],
end

theorem lemma_2 {a b p q :ℤ}:int.prime (p*p+q*q)→ (p*p+q*q) ∣ (a*a + b*b) → ∃ x y:ℤ,(x*x+y*y)*(p*p+q*q)=(a*a+b*b):=begin
    intros  H1 H2,
    have H3:(p*p+q*q) ∣ (b*p-a*q)*(b*p+a*q):=begin
        rw[mul_add,sub_mul,sub_mul,add_sub],
        have H3:a * q * (b * p) =b * p * (a * q):=by rw mul_comm (a*q),
        rw H3,rw sub_add_cancel,clear H3,
        have H3:b * p * (b * p) - a * q * (a * q)=(p*p)*(a*a+b*b)-(a*a)*(p*p+q*q):=by rw[mul_add,mul_add];admit,
        rw H3,exact dvd_sub (dvd_mul_of_dvd_right H2 _) (dvd_mul_left _ _),
    end,
    rw prime_dvd_mul H1 at H3,revert a b p q H1 H2 H3,
    have H:∀ a b p q:ℤ,int.prime (p * p + q * q)→p * p + q * q ∣ a * a + b * b→ p * p + q * q ∣ b * p - a * q→∃ (x y : ℤ), (x * x + y * y) * (p * p + q * q) = a * a + b * b:=begin
        assume a b p q H1 H2 H3,
        have H4:=dioph_identity b a q p,
        have H5:=dvd_mul_left (p * p + q * q) (b * b + a * a),rw [add_comm (p*p),H4,add_comm (q*q)] at H5,
        have H6:=iff.elim_right (dvd_add_iff_left (dvd_mul_of_dvd_right H3 (b * p - a * q))) H5,clear  H5,
        have H7:=mul_dvd_mul H3 H3, have H8:=exists_eq_mul_left_of_dvd H3,cases H8 with c Hc,
        cases exists_eq_mul_left_of_dvd H2 with d Hd,
        have H10:(b * b + a * a) * (q * q + p * p) = d*  (q * q + p * p) * (q * q + p * p):=begin rw[add_comm(b*b),Hd],simp,end,rw H10 at H4,clear H10,
        have H10:=dvd_mul_left ((q * q + p * p) * (q * q + p * p) ) d,
        rw[←mul_assoc,H4,add_comm (q*q),←dvd_add_iff_left H7] at H10,have H11:= dvd_of_mul_left_dvd H10,rw prime_dvd_mul at H11,simp at H11,
        cases exists_eq_mul_left_of_dvd H11 with e He,rw [add_comm(q*q),←Hd] at H4,
        existsi [c,e],clear H10 H2 H6 H3 H7 Hd d,
        suffices :(c * c + e * e) * (p * p + q * q) * (p * p + q * q) = (a * a + b * b) * (p * p + q * q),
        have H3:(p*p + q*q)≠0:=begin intro,unfold int.prime at H1,rw a_1 at H1,revert H1,simp [int.nat_abs_zero,nat.prime,(dec_trivial:¬0≥2)],end,
        have H2:(c * c + e * e) * (p * p + q * q) * (p * p + q * q) / (p * p + q * q)= (a * a + b * b) * (p * p + q * q) / (p * p + q * q):=by rw this,
        rwa[int.mul_div_cancel ((c * c + e * e) * (p * p + q * q)) H3,int.mul_div_cancel (a * a + b * b) H3] at H2,rw H4,
        have H12:(c * c + e * e) * (p * p + q * q) * (p * p + q * q) = (c * (p * p + q * q))*(c * (p * p + q * q))+ (e * (p * p + q * q))*(e * (p * p + q * q)):=begin
            rw [add_mul _ _ (p * p + q * q),add_mul _ _ (p * p + q * q)],norm_num,end,
        rw [H12,←Hc,←He],norm_num,assumption,
    end,intros a b p q H1 H2 H3,cases H3 with H3 H3,exact H a b p q H1 H2 H3,
    have H4:p * p + q * q ∣ -a * -a + b * b:=by rwa neg_mul_neg,
    have H5:p * p + q * q ∣ b * p - -a * q:=by revert H3;simp;assumption,
    have H6:=H (-a) b p q H1 H4 H5,rwa neg_mul_neg at H6,
end
theorem lemma_2_nat  {a b p q :ℕ}:nat.prime (p*p+q*q)→ (p*p+q*q) ∣ (a*a + b*b) → ∃ x y:ℕ,(x*x+y*y)*(p*p+q*q)=(a*a+b*b):=begin
    assume hp h,rw [←int.coe_nat_dvd,int.coe_nat_add,int.coe_nat_add,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_mul] at h,
    have:int.prime ↑(p * p + q * q),unfold int.prime,rwa int.nat_abs_of_nat,
    rw [int.coe_nat_add,int.coe_nat_mul,int.coe_nat_mul] at this,have:=lemma_2 this h,cases this with x hx, cases hx with y hxy,
    existsi [int.nat_abs x,int.nat_abs y],rw [←int.coe_nat_eq_coe_nat_iff,int.coe_nat_mul,int.coe_nat_add,int.coe_nat_add,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_add,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_mul],
    rwa[←int.abs_eq_nat_abs,←int.abs_eq_nat_abs,abs_mul_abs_self,abs_mul_abs_self],
end

open list
open nat
theorem prime_induction (n:ℕ) {q : ℕ → Prop} : n > 0 → q 1 → (∀ m p:ℕ, prime p → q m → q (m * p)) → q n:=begin
    revert n,have:∀ y n:ℕ, n≤y→ n > 0 → q 1 → (∀ m p:ℕ, prime p → q m → q (m * p)) → q n,
    assume y n hny hn q1 hmp,cases n,simp[(dec_trivial:¬0>0)] at hn,contradiction,revert n,induction y with y1 hi,assume n hny hn,simp[(dec_trivial:¬succ n≤0)] at hny,contradiction,
    assume n hny hn,cases n,assumption,cases exists_prime_and_dvd (dec_trivial:succ(succ n)≥2) with p hp,
    cases exists_eq_mul_left_of_dvd hp.right with c hc,cases c,simp [(dec_trivial:¬succ (succ n) = 0)]at hc,contradiction,
    have:=iff.elim_right (lt_mul_iff_one_lt_right (dec_trivial:succ c > 0)) (prime.gt_one hp.left),rw ←hc at this,have:=le_of_succ_le_succ (le_trans (succ_le_of_lt this) hny),
    have :=hmp (succ c) p hp.left (hi c this dec_trivial),rwa hc,exact λ n,this n n (le_refl n),
end
theorem dvd_prime {x y p:ℕ}:prime p→x ∣ p * y → p ∣ x ∨ x ∣ y:=begin
    cases x,simp,have hy:succ x>0:=dec_trivial,generalize hu :succ x = u,revert y p,
    apply prime_induction u,rwa hu at hy,simp,assume m p1 hp1 hi y p2 hp2 hd,
    have:=dvd_of_mul_right_dvd hd,cases hi hp2 this,simp [dvd_mul_of_dvd_left h p1],
    
end

theorem lemma_3:∀ n x a b:ℕ,x*n=a*a+b*b→(∀x₁ x₂,¬x=x₁ *x₁+x₂ * x₂)→∃ p:ℕ,p∣n∧(∀p₁ p₂:ℕ,¬p=p₁*p₁+p₂*p₂):=begin
    have: ∀ (L:list ℕ) (x a b:ℕ),x * prod L = a*a+b*b →(∀ p:ℕ,p∈L→nat.prime p)→(∀ x₁ x₂:ℕ, x≠x₁ *x₁+x₂ * x₂)→∃ p:ℕ,p∣prod L∧(∀ p₁ p₂:ℕ,p≠p₁*p₁+p₂*p₂):=begin
        assume L,induction L with p1 L hi,simp,intros,have:=a_2 a b a_1,contradiction,simp,
        assume x a b hab hp hL hxs,cases classical.em (∃ p₁ p₂:ℕ, p₁*p₁ +p₂*p₂=p1),
        cases h with p₁ hp12, cases hp12 with p₂ hp12,rw[mul_comm p1,←mul_assoc] at hab,
        have h1:=dvd_mul_left p1 (x*prod L),rw hab at h1,rw ← hp12 at hp h1,have h2:=lemma_2_nat hp h1,
        cases h2 with ai hai, cases hai with bi habi,
        rw [hp12,←hab] at habi,have h2:((ai * ai + bi * bi) * p1)/p1=(x * prod L * p1)/p1,rw habi,rw hp12 at hp,rw [nat.mul_div_cancel _ (prime.pos hp),nat.mul_div_cancel _ (prime.pos hp)] at h2,
        rw eq_comm at h2,have:= hi x ai bi h2 hL hxs,cases this with k hk,existsi k,
        simp[hk.right, dvd_mul_of_dvd_right hk.left p1],existsi p1,simp,simp at h,intros d e,
        have:= h d e,rwa eq_comm,
    end,
    assume n x a b hnx hx,
    admit,
end
theorem lemma_4 {a b:ℕ} (f:ℕ):coprime a b→f∣(a*a+b*b)→∃x y:ℕ,x*x+y*y = f:=begin
    assume hco hf,apply classical.by_contradiction,simp,assume hxx,have h1:=exists_eq_mul_left_of_dvd hf,
    cases h1 with c hc,
end