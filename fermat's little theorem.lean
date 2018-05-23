import data.nat.modeq data.nat.basic data.nat.prime data.int.basic tactic.norm_num
def prime : ℤ → Prop := λ x,nat.prime (int.nat_abs x)

theorem prime_dvd_mul {p m n : ℤ} (pp : prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=begin
    have H:int.nat_abs p ∣int.nat_abs m * int.nat_abs n ↔ int.nat_abs p ∣ int.nat_abs m ∨ int.nat_abs p ∣int.nat_abs n:=begin
        unfold prime at pp,revert pp, exact nat.prime.dvd_mul,end,
    rw [←int.coe_nat_dvd,←int.coe_nat_dvd,←int.coe_nat_dvd,int.coe_nat_mul,int.nat_abs_dvd,int.nat_abs_dvd,int.nat_abs_dvd,
    ←int.abs_eq_nat_abs,←int.abs_eq_nat_abs] at H,cases lt_trichotomy m 0 with Hm Hm,
    cases lt_trichotomy n 0 with Hn Hn,rwa[abs_of_neg Hm,abs_of_neg Hn,dvd_neg,dvd_neg,neg_mul_neg] at H,
    cases Hn with Hn Hn,rw Hn,norm_num,rwa[abs_of_neg Hm,abs_of_pos Hn,dvd_neg,←neg_mul_eq_neg_mul,dvd_neg] at H,
    cases Hm with Hm Hm,rw Hm,simp,cases lt_trichotomy n 0 with Hn Hn,rwa[abs_of_neg Hn,abs_of_pos Hm,dvd_neg,mul_neg_eq_neg_mul_symm,dvd_neg] at H,
    cases Hn with Hn Hn,rw Hn,simp,rwa[abs_of_pos Hn,abs_of_pos Hm] at H,
end
theorem dioph_identity:∀ a b p q:ℤ, (a*a+b*b)*(p*p+q*q)=(a*p+b*q)*(a*p+b*q)+(a*q-b*p)*(a*q-b*p):=begin
    intros,rw[mul_add,mul_add,add_mul,add_mul,add_mul,add_mul,mul_sub,sub_mul,sub_mul],norm_num,
end
theorem lemma_1 : ∀ a b p q : ℤ,∃ x y:ℤ, x*x+y*y=(a*a+b*b)*(p*p+q*q):=begin
    intros,existsi [(a*p+b*q),(a*q-b*p)],
    rw [mul_add,mul_add,add_mul,add_mul,add_mul,add_mul,mul_sub,sub_mul,sub_mul],norm_num,
end

theorem lemma_2 : ∀ (a b p q :ℤ), prime (p*p+q*q)→ (p*p+q*q) ∣ (a*a + b*b) → ∃ x y:ℤ,(x*x+y*y)*(p*p+q*q)=(a*a+b*b):=begin
    intros a b p q H1 H2,
    have H3:(p*p+q*q) ∣ (b*p-a*q)*(b*p+a*q):=begin
        rw[mul_add,sub_mul,sub_mul,add_sub],
        have H3:a * q * (b * p) =b * p * (a * q):=by norm_num,
        rw H3,rw sub_add_cancel,clear H3,
        have H3:b * p * (b * p) - a * q * (a * q)=(p*p)*(a*a+b*b)-(a*a)*(p*p+q*q):=by rw[mul_add,mul_add];norm_num,
        rw H3,exact dvd_sub (dvd_mul_of_dvd_right H2 _) (dvd_mul_left _ _),
    end,
    rw prime_dvd_mul H1 at H3,revert a b p q H1 H2 H3,
    have H:∀ a b p q:ℤ,prime (p * p + q * q)→p * p + q * q ∣ a * a + b * b→ p * p + q * q ∣ b * p - a * q→∃ (x y : ℤ), (x * x + y * y) * (p * p + q * q) = a * a + b * b:=begin
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
        have H3:(p*p + q*q)≠0:=begin intro,unfold prime at H1,rw a_1 at H1,revert H1,simp [int.nat_abs_zero,nat.prime,(dec_trivial:¬0≥2)],end,
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

open list
open nat
theorem squares_nat_int{a:ℕ}:(∃ x y:ℤ, x*x+y*y = ↑a)→∃x y:ℕ, x*x+y*y = a:=begin
    simp,assume x y hxy,existsi [(int.nat_abs x),int.nat_abs y],rw [←int.coe_nat_eq_coe_nat_iff,int.coe_nat_add,int.coe_nat_mul,int.coe_nat_mul],
    rwa[←int.abs_eq_nat_abs,←int.abs_eq_nat_abs, abs_mul_abs_self,abs_mul_abs_self],
end
theorem lemma_3:∀ n x:ℕ,x∣n→(¬∃x₁ x₂, x=x₁ *x₁+x₂ * x₂)→∃ p:ℕ,(p*x)∣n∧(¬∃p₁ p₂:ℕ,(p₁*p₁+p₂*p₂)=p):=begin
    have: ∀ (L:list ℕ) (x a b:ℕ),x * prod L = a*a+b*b →(∀ p:ℕ,p∈L→nat.prime p)→x∣prod L→(∀ x₁ x₂:ℕ, x≠x₁ *x₁+x₂ * x₂)→∃ p:ℕ,(p*x)∣prod L∧(∀ p₁ p₂:ℕ,p≠p₁*p₁+p₂*p₂):=begin
        assume L,induction L with p1 L hi,simp,intros,have:=a_3 a b a_1,contradiction,simp,
        assume x a b hab hp hL hx hxs,cases classical.em (∃ p1₁ p1₂:ℕ,p1₁ *p1₁ +p1₂ *p1₂ =p1),
        cases h with p1₁,cases h_h with p1₂,rw ←h_h_h at hp,rw [mul_comm,mul_assoc,←h_h_h]at hab,
        have pdvd:=dvd_mul_right (p1₁ * p1₁ + p1₂ * p1₂) (prod L * x),rw [hab,←int.coe_nat_dvd,int.coe_nat_add,int.coe_nat_add,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_mul,int.coe_nat_mul] at pdvd,have:=lemma_2 a b p1₁ p1₂ hp pdvd,
        cases this with x₁ hx1,cases hx1 with y₁ hxy,have:∃ x₂ y₂:nat,x*prod L = x₂*x₂+y₂*y₂,
        existsi [int.nat_abs x₁,int.nat_abs y₁],rw[←int.coe_nat_mul,←int.coe_nat_mul,←int.coe_nat_mul,←int.coe_nat_mul,←int.coe_nat_add,←int.coe_nat_add,←hab,int.coe_nat_mul,mul_comm] at hxy,
        have: (↑(p1₁ * p1₁ + p1₂ * p1₂) * (x₁ * x₁ + y₁ * y₁)) / ↑(p1₁ * p1₁ + p1₂ * p1₂)=(↑(p1₁ * p1₁ + p1₂ * p1₂) * ↑(prod L * x)) / ↑(p1₁ * p1₁ + p1₂ * p1₂),rw hxy,rw [int.mul_div_cancel_left,int.mul_div_cancel_left] at this,
        rw[mul_comm x,←int.coe_nat_eq_coe_nat_iff,← this,int.coe_nat_add,int.coe_nat_mul,int.coe_nat_mul,←int.abs_eq_nat_abs,← int.abs_eq_nat_abs,abs_mul_abs_self,abs_mul_abs_self],rw [h_h_h,←int.coe_nat_zero,ne.def,int.coe_nat_eq_coe_nat_iff],have:=prime.pos hp,intro,rw[h_h_h, a_1] at this,revert this,exact dec_trivial,
        rw [h_h_h,←int.coe_nat_zero,ne.def,int.coe_nat_eq_coe_nat_iff],have:=prime.pos hp,intro,rw[h_h_h, a_1] at this,revert this,exact dec_trivial,
        clear hxy x₁ y₁,cases this with x₁ hxy,cases hxy with y₁ hxy,have:= hi x x₁ y₁ hxy hL,
end
