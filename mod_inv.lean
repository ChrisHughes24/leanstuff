import data.nat.basic data.int.basic data.nat.modeq tactic.norm_num data.nat.prime
namespace nat 

def mod_inv_aux : ℕ → ℕ → ℤ
| 0        p := 0
| (succ m) p := have (p%succ m)<succ m:=mod_lt p (succ_pos m),
(↑(gcd (succ m) p) - (mod_inv_aux (p%succ m) (succ m)*↑p))/↑(succ m)
def mod_inv : ℕ → ℕ → ℕ := λ m p, int.nat_abs (mod_inv_aux m p % (↑(p/gcd m p)))

theorem mod_inv_aux_bezout :∀ a b:ℕ,mod_inv_aux a b * ↑a +mod_inv_aux (b%a) a * ↑b = gcd a b:=begin 
    assume m p,rw add_comm,apply gcd.induction m p,assume n,rw mod_zero,simp[mod_inv_aux],cases n with n,simp [mod_inv_aux],simp [mod_inv_aux],rw int.div_self,norm_num,
    rw [←int.coe_nat_zero,add_comm,int.coe_nat_add_one_out,int.coe_nat_eq_coe_nat_iff],exact dec_trivial,intros m1 p1,cases m1 with m1,intros,exfalso,revert a,exact dec_trivial,
    have: mod_inv_aux (succ m1) p1 = (↑(gcd (succ m1) p1) - mod_inv_aux (p1 % succ m1) (succ m1) * ↑p1) / ↑(succ m1):=by unfold mod_inv_aux,
    rw this,assume H H1,rw [eq_comm,←sub_eq_iff_eq_add] at H1,unfold gcd,
    rw[int.mod_def,mul_sub,←sub_add,eq_comm,←sub_eq_iff_eq_add,mul_comm _ (↑p1 / ↑(succ m1)),←mul_assoc,←sub_mul] at H1,rw ←H1,rw int.mul_div_cancel,rw [sub_mul,sub_eq_iff_eq_add] at H1,
    rw [sub_mul,H1],norm_num,rw[←int.coe_nat_zero,add_comm,int.coe_nat_add_one_out,int.coe_nat_eq_coe_nat_iff],exact dec_trivial,
end

theorem mod_inv_gcd :∀ m p:ℕ,p>0→ m * mod_inv m p ≡ gcd m p [MOD p]:=begin
    unfold mod_inv,assume m p Hp,rw modeq.modeq_iff_dvd,
    have H2:∀ x y:ℤ, x%y = x - y * (x/y) :=begin assume x y, rw[eq_comm,sub_eq_iff_eq_add,eq_comm],apply int.mod_add_div, end,
    rw [←mod_inv_aux_bezout,int.coe_nat_mul, ←int.abs_eq_nat_abs,abs_of_nonneg, H2,mul_sub],simp,rw [←add_assoc,←add_assoc,mul_comm (↑m),add_comm (mod_inv_aux m p * ↑m)],simp,
    have : p ∣ (p/gcd m p) * m:=begin cases exists_eq_mul_right_of_dvd (and.left(gcd_dvd m p)) with c Hc,
    have : p / gcd m p * m= p /gcd m p *gcd m p * c:=by rw[mul_assoc,←Hc],rw this,rw nat.div_mul_cancel (and.right(gcd_dvd m p)),simp,end,
    apply dvd_add,simp,rw ←int.coe_nat_dvd at this,rw [←mul_assoc,←int.coe_nat_mul,mul_comm m],apply dvd_mul_of_dvd_left this,
    apply int.mod_nonneg,cases exists_eq_mul_left_of_dvd (and.right(gcd_dvd m p)) with c Hc,have :p / gcd m p=c*gcd m p/gcd m p:= by rw ←Hc,rw this,rw nat.mul_div_cancel,intro,rw [←int.coe_nat_zero,int.coe_nat_eq_coe_nat_iff] at a,rw a at Hc,simp at Hc,rw Hc at Hp,revert Hp,exact dec_trivial,
    apply gcd_pos_of_pos_right m Hp,
end
theorem mod_inv_unique :∀ m n p:ℕ,p>0→ coprime m p→ (m * n ≡ 1 [MOD p] ↔ n ≡ mod_inv m p [MOD p]):=begin
    assume m n p Hp Hc,apply iff.intro,assume H,
    have H1:= modeq.modeq_mul (modeq.refl (mod_inv m p)) H,
    rw [←mul_assoc,mul_comm _ m] at H1,have H2:=modeq.trans (modeq.symm(modeq.modeq_mul (mod_inv_gcd m p Hp) (modeq.refl n))) H1,
    rw coprime.gcd_eq_one Hc at H2,simp at H2,exact H2,intro, have :=modeq.trans (modeq.modeq_mul (modeq.refl m) a) (mod_inv_gcd m p Hp),
    rw coprime.gcd_eq_one Hc at this,assumption,
end
theorem modeq_mul_cancel{ a b c p:ℕ}:p > 0 → coprime a p → (a * b ≡ a * c [MOD p] ↔ b ≡ c [MOD p]):=begin
    assume H0 Hco,apply iff.intro,assume H, have H1:=modeq.modeq_mul (modeq.refl (mod_inv a p)) H,rw[←mul_assoc,←mul_assoc] at H1,
    have Hb:=modeq.symm (modeq.modeq_mul (mod_inv_gcd a p H0) (modeq.refl b)),
    have Hc:=(modeq.modeq_mul (mod_inv_gcd a p H0) (modeq.refl c)),rw [coprime.gcd_eq_one Hco,one_mul,mul_comm a] at *,
    exact modeq.trans (modeq.trans Hb H1) Hc,exact modeq.modeq_mul (modeq.refl a),
end
theorem modeq_zero:∀ a b:ℕ, a ≡ b [MOD 0] ↔ a = b:=λ a b, by simp[modeq]
open list
theorem modeq_prod_list : ∀ (A B : list ℕ) (z:ℕ),(∀y:ℕ,countp (λ x,x ≡ y [MOD z]) A = countp (λ x,x ≡ y [MOD z]) B)→ prod A ≡ prod B [MOD z]:=begin
    intros A B z H,revert B,
    induction A with p A1 Hi,intros B H,
    simp,simp at H,cases B with b B,simp,exfalso, have:= H b,rw list.countp_cons_of_pos at this,
    have H:list.countp (λ (x : ℕ), x ≡ b [MOD z]) B + 1≥1:=le_add_left _ _,rw ←this at H,revert H,exact dec_trivial,
    apply modeq.refl,intros B H,have H1:= H p,rw list.countp_cons_of_pos at H1,have H2:0<list.countp (λ (x : ℕ), x ≡ p [MOD z]) A1 + 1:=le_add_left _ _,
    rw H1 at H2,rw list.countp_pos at H2,cases H2 with q Hq,cases Hq with Hq Hq1,
    have H2:(∀ (y : ℕ),
    list.countp (λ (x : ℕ), x ≡ y [MOD z]) A1 = list.countp (λ (x : ℕ), x ≡ y [MOD z]) (list.erase B q)):=begin
        intro y,have H2:= H y,have H3:=perm_erase Hq,have H4:=perm_countp (λ (x : ℕ), x ≡ y [MOD z]) H3,
        cases decidable.em (p ≡ y [MOD z]) with A A,rw countp_cons_of_pos at H2,rw[H4,countp_cons_of_pos] at H2,apply add_right_cancel H2,exact modeq.trans Hq1 A,assumption,
        rw list.countp_cons_of_neg at H2,rwa[H4,countp_cons_of_neg] at H2,intro,have H3:=modeq.symm Hq1,exact A (modeq.trans H3 a),assumption,
    end,have H3:=Hi(list.erase B q) H2,have H4:=prod_eq_of_perm (perm_erase Hq),rw [H4,prod_cons,prod_cons],exact modeq.modeq_mul (modeq.symm Hq1) H3,apply modeq.refl,
end
def Lb : ℕ → ℕ → list ℕ 
| 0 b := list.nil
| (succ n) b := (b*succ n):: Lb n b

theorem L3 :∀(A B:list ℕ)(p:ℕ),(∀a:ℕ,a∈A→∃(b:ℕ)(H:b∈B),b≡a[MOD p])→(∀b:ℕ,b∈B→∃(a:ℕ)(H:a∈A),a≡b[MOD p])→(∀a₁ a₂:ℕ,a₁∈A→a₂∈list.erase A a₁→¬a₁≡a₂[MOD p])→(∀b₁ b₂:ℕ,b₁∈B→b₂∈list.erase B b₁→¬b₁≡b₂[MOD p])→(∀y:ℕ,countp(λa,a≡y[MOD p])A=countp(λb,b≡y[MOD p])B):=begin
    assume A B p HA HB HA1 HB1 y,
    cases decidable.em(∃(b:ℕ)(H:b∈B),b≡y[MOD p]) with Hb Hb,
    apply exists.elim Hb, assume b1 Hb1, cases Hb1 with Hb1 Hb2,
    have Ha:= HB b1 Hb1,
    apply exists.elim Ha, assume a1 H,cases H with Ha1 Ha2,
    have Hb:= HA a1 Ha1,
    rw [perm_countp _ (perm_erase Hb1),perm_countp _ (perm_erase Ha1),countp_cons_of_pos,countp_cons_of_pos],
    cases decidable.em (0<countp (λ (a : ℕ), a ≡ y [MOD p]) (list.erase A a1)) with Ha4 Ha4,
    exfalso,rw countp_pos at Ha4,cases Ha4 with a₂ Ha₂,cases Ha₂ with ha₂ Ha₂,have:=HA1 a1 a₂ Ha1 ha₂,
    exact this (modeq.trans (modeq.trans Ha2 Hb2) (modeq.symm Ha₂)),
    cases decidable.em (0<countp (λ (b : ℕ), b ≡ y [MOD p]) (list.erase B b1)) with Hb4 Hb4,
    exfalso,rw countp_pos at Hb4,cases Hb4 with b₂ Hb₂,cases Hb₂ with hb₂ Hb₂,have:=HB1 b1 b₂ Hb1 hb₂,
    exact this (modeq.trans Hb2 (modeq.symm Hb₂)),
    rw [eq_zero_of_le_zero (le_of_not_gt Ha4),eq_zero_of_le_zero (le_of_not_gt Hb4)],assumption,exact modeq.trans Ha2 Hb2,

    cases decidable.em(∃(a:ℕ)(H:a∈A),a≡y[MOD p])with H2 H2,
    cases H2 with a1 HA1,cases HA1 with HA1 HA2,exfalso,
    cases (HA a1 HA1) with b1 Hb1,cases Hb1 with Hb1 Hb2,
    exact Hb (exists.intro b1 (exists.intro Hb1 (modeq.trans Hb2  HA2))),

    rw ←countp_pos at H2 Hb,
    have H1:= eq_zero_of_le_zero (le_of_not_gt Hb),have H2:=eq_zero_of_le_zero (le_of_not_gt H2),
    rw[H1, ←H2]
end
theorem modeq_mod_cancel:∀ a p:nat, a % p ≡ a [MOD p] :=begin
    assume a p,rw modeq.modeq_iff_dvd,rw [int.coe_nat_mod,int.mod_def],norm_num,
end
theorem mem_Lb :∀ k p b:ℕ,b>0→(k*b∈Lb (p-1) b↔k>0∧k<p):=begin
    assume k p b Hb,induction p with p1,simp [Lb],intro,exact dec_trivial,
    cases p1 with p2, simp[Lb],intro,apply le_of_lt_succ,apply succ_lt_succ,assumption,
    simp[Lb],apply iff.intro, assume H, cases H,rw[mul_comm,nat.mul_left_inj Hb] at H,rw H,apply and.intro,exact dec_trivial,exact lt_succ_self _,
    rw succ_sub_one at p_ih, simp [H] at p_ih, exact ⟨p_ih.left,lt_trans p_ih.right (lt_succ_self _)⟩,
    cases decidable.em (k<succ p2),intro,simp [a,h] at p_ih,simp[p_ih],intro,rw[mul_comm,nat.mul_left_inj Hb],have:=le_of_not_gt h,simp [le_antisymm (le_of_not_gt h) (le_of_succ_le_succ (succ_le_of_lt a.right))],
end
theorem Lb_dvd:∀ p b a:ℕ,a ∈ Lb (p-1) b→∃ k,k*b=a∧k>0∧k<p:=begin
    assume p b a,induction p with p1,simp [Lb],simp[Lb],cases p1 with p2,simp[Lb],simp[Lb],assume H,cases H,existsi succ p2,simp[H],rw mul_comm,exact ⟨rfl,dec_trivial,lt_succ_self (succ p2)⟩,
    rw succ_sub_one at p_ih,cases p_ih H,existsi w,exact ⟨h.left,h.right.left,lt_trans h.right.right (lt_succ_self (succ p2))⟩,
end
theorem L1Lb : ∀ p c:ℕ,c>0→ prime p → coprime c p→ (∀a:ℕ,a∈(Lb (p-1) 1)→∃(b:ℕ)(H:b∈(Lb (p-1) c)),b≡a[MOD p])∧(∀b:ℕ,b∈(Lb (p-1)c)→∃(a:ℕ)(H:a∈(Lb (p-1) 1)),a≡b[MOD p]):=begin
    assume p c Hc Hp Hco,have Hp0:=lt_trans (dec_trivial:0<1) (prime.gt_one Hp),apply and.intro,assume a Ha,have Hp0:=lt_trans (dec_trivial:0<1) (prime.gt_one Hp),
    existsi (a*mod_inv c p)%p*c,rw mem_Lb _ _ _ Hc,simp[mod_lt (a * mod_inv c p) Hp0],
    have H:=mod_inv_gcd c p Hp0,rw coprime.gcd_eq_one Hco at H,
    have H1:a * ( c*mod_inv c p ) ≡ a *1 [MOD p]:=modeq.modeq_mul (modeq.refl a) H,rw[mul_comm c,←mul_assoc,mul_one] at H1,
    have H4:=modeq_mod_cancel (a * mod_inv c p) p,
    have H2:=modeq.modeq_mul (modeq_mod_cancel (a * mod_inv c p) p) (modeq.refl c),
    have H3:=modeq.trans H2 H1,simp[H3],cases decidable.em(a * mod_inv c p % p = 0),exfalso,rw [←dvd_iff_mod_eq_zero,prime.dvd_mul Hp] at h,rw[←mul_one a,mem_Lb]at Ha,
    have:=mod_eq_of_lt Ha.right,rw dvd_iff_mod_eq_zero at h,rw this at h,simp[ne_of_gt Ha.left] at h,
    rw ←modeq.modeq_zero_iff at h,have :=modeq.symm(modeq.trans (modeq.symm(modeq.modeq_mul (modeq.refl c) h)) H), simp at this,rw modeq.modeq_zero_iff at this,exact prime.not_dvd_one Hp this,
    exact dec_trivial,cases a * mod_inv c p % p,revert h,simp,exact dec_trivial,
    assume a Ha,existsi a%p,rw [←mul_one (a%p),mem_Lb _ _ _ (dec_trivial:1>0)],simp,simp[mod_lt a Hp0,modeq_mod_cancel a p],
    cases decidable.em(a % p = 0),exfalso, rw[←dvd_iff_mod_eq_zero] at h,cases Lb_dvd _ _ _ Ha,rw [←h_1.left,prime.dvd_mul] at h,cases h,have:= mod_eq_of_lt h_1.right.right,rw dvd_iff_mod_eq_zero at h,rw h at this,rw ←this at h_1,exact (dec_trivial:¬0<0) h_1.right.left,
    have:= coprime.eq_one_of_dvd (coprime.symm Hco) h,rw this at Hp,revert Hp, simp[prime],exact dec_trivial,assumption,cases a%p,exfalso,revert h,exact dec_trivial,exact dec_trivial,
end

theorem Lb_ne: ∀ (p c k :nat), c>0→(k>0→k<p→count (k*c) (Lb (p-1) c) = 1)∧(k≥p→count (k*c) (Lb (p-1) c) = 0):=begin
    assume p c k Hc,induction p with p1 Hi,simp [Lb],intro,exact not_lt_zero k,cases p1 with p2,simp[Lb],intro,have:=succ_le_of_lt a,intro,exact not_lt_of_ge this a_1,
    have Hkp1:k<succ(succ p2) ↔k=succ p2 ∨ k<succ p2:=begin
        rw ←le_iff_eq_or_lt,rw ←succ_le_succ_iff,apply iff.intro,
        intro, apply succ_le_of_lt a,intro, apply lt_of_succ_le a,
    end, rw Hkp1,apply and.intro,
    assume Hk Hkp,clear Hkp1,cases Hkp,simp at Hi,rw ←Hkp at Hi,have:=Hi.right (le_refl k),simp [Lb],rw [←Hkp,mul_comm,count_cons_self,mul_comm,this],
    simp at Hi,simp[Lb],rw count_cons_of_ne,exact Hi.left Hk Hkp,rw mul_comm,rw ←mul_lt_mul_left Hc at Hkp,exact ne_of_lt Hkp,
    assume H,have:= Hi.right (ge_trans H (le_succ _)),simp[Lb],simp at this,rwa count_cons_of_ne,
    have:=lt_of_lt_of_le (lt_succ_self (succ p2)) H,rw ←mul_lt_mul_left Hc at this,rw mul_comm,apply ne.symm, exact ne_of_lt this,
end
theorem ladida:∀ c a b p:ℕ,coprime c p →a>0→a<p→b>0→b<p→p>0→(c*a ≡ c*b [MOD p] ↔ a = b):=begin
    assume c a b p Hco Ha0 Hap Hb0 Hbp Hp0,apply iff.intro,
    assume Hc,have:=@modeq_mul_cancel c b a p Hp0 Hco,have Hc1:=modeq.symm Hc,rw this at Hc1,clear Hc,
    simp[modeq] at Hc1,rw [mod_eq_of_lt Hap,mod_eq_of_lt Hbp] at Hc1,rw Hc1,intro,rw a_1,
end

theorem not_modeq_list:∀ p b:ℕ,coprime b p→p>0→b>0→(∀a₁ a₂:ℕ,a₁∈Lb (p-1) b→a₂∈list.erase (Lb (p-1) b) a₁→¬a₁≡a₂[MOD p]):=begin
    assume p b Hp Hp0 Hb a₁ a₂ Ha₁ Ha₂,have ha₁:=Lb_dvd _ _ _ Ha₁,have H1:=perm_count (perm_erase Ha₁) a₂,have H2:=iff.elim_right count_pos Ha₂,
    rw count_cons' at H1,have:=lt_of_lt_of_le H2 (le_add_right _ (ite (a₂ = a₁) 1 0)),rw ←H1 at this,rw count_pos at this,
    have ha₂:=Lb_dvd _ _ _ this,
    have :¬a₁=a₂:=begin
        cases ha₁ with k₁ Hk₁,cases ha₂ with k₂ Hk₂,rw ←Hk₁.left at Ha₁,rw ←Hk₂.left at Ha₂,clear H1,
        have hk₂:=(Lb_ne p b k₂ Hb).left Hk₂.right.left Hk₂.right.right,
        rw perm_count (perm_erase Ha₁) at hk₂,rw Hk₁.left at Ha₁ hk₂, rw Hk₂.left at hk₂ Ha₂,
        assume H,rw [←H,←count_pos] at Ha₂,rw [H,count_cons_self] at hk₂,have :=succ_inj hk₂,rw [H,this] at Ha₂,
        revert Ha₂,exact dec_trivial,
    end,
    cases ha₁ with k₁ Hk₁,cases ha₂ with k₂ Hk₂,rw [←Hk₁.left,←Hk₂.left],
    rw[mul_comm,mul_comm k₂,ladida b k₁ k₂ p Hp Hk₁.right.left Hk₁.right.right Hk₂.right.left Hk₂.right.right Hp0],
    rw [←Hk₁.left,←Hk₂.left] at this,intro,rw a at this,revert this,simp,
end
theorem fact_list :∀ p k:ℕ,p>0→prod (Lb p k)=k^p*fact p:=begin
    assume p k,induction p with p1,simp [(dec_trivial:¬0>0)],cases p1 with p2,simp[Lb],simp[Lb,fact,pow],simp[Lb,fact,pow] at p_ih,intro,
    have:=p_ih dec_trivial,rw this,cc,
end
theorem prime_not_dvd_fact : ∀ p k:ℕ,k<p → prime p→¬p∣fact k:=begin
    assume p k, induction k with k1,simp [fact,prime],intros,intro,rw a_3 at a_1,revert a_1,exact dec_trivial,
    assume H H1,simp[fact],assume H3,rw prime.dvd_mul H1 at H3,cases H3,
    rw [dvd_iff_mod_eq_zero] at H3,rw mod_eq_of_lt H at H3,revert H3,exact dec_trivial,
    exact k_ih (lt_trans (lt_succ_self _) H) H1 H3,
end


theorem fermats_little_theorem1 :∀ a p:ℕ,prime p→ coprime a p → a^(p-1) ≡ 1 [MOD p]:=begin
    assume b p Hp Hpc,have Hp1:(p-1)>0:=nat.sub_pos_of_lt (lt_of_lt_of_le (dec_trivial:1<2) Hp.left),
    have Hp0:p>0:=by unfold prime at Hp;exact lt_of_lt_of_le (dec_trivial:0<2) Hp.left,
    rw [←@modeq_mul_cancel (fact(p-1)) (b^(p-1)) 1 p Hp0,mul_comm,mul_comm (fact (p-1)),←fact_list _ _ Hp1],have:∀ p:ℕ, 1=1^p := begin assume p,induction p,simp,rw pow_succ,simp,assumption, end,
    have H:1 * fact (p - 1) = 1^(p-1) * fact(p-1):=by rw ←this,rw H, clear H this,rw ←fact_list _ _ Hp1,
    suffices: (∀y:ℕ,countp (λ x,x ≡ y [MOD p]) (Lb (p - 1) b) = countp (λ x,x ≡ y [MOD p]) (Lb (p - 1) 1)),
    exact modeq_prod_list (Lb (p - 1) b) (Lb (p - 1) 1) p this,revert b, assume c Hpc,
    suffices :(∀a:ℕ,a∈(Lb (p - 1) c)→∃(b:ℕ)(H:b∈(Lb (p - 1) 1)),b≡a[MOD p])∧(∀b:ℕ,b∈(Lb (p - 1) 1)→∃(a:ℕ)(H:a∈(Lb (p - 1) c)),a≡b[MOD p])∧(∀a₁ a₂:ℕ,a₁∈(Lb (p - 1) c)→a₂∈list.erase (Lb (p - 1) c) a₁→¬a₁≡a₂[MOD p])∧(∀b₁ b₂:ℕ,b₁∈(Lb (p - 1) 1)→b₂∈list.erase (Lb (p - 1) 1) b₁→¬b₁≡b₂[MOD p]),
    exact L3 (Lb (p - 1) c) (Lb (p - 1) 1) p this.left this.right.left this.right.right.left this.right.right.right,
    suffices Hc:c>0,rw ←and.assoc, apply and.intro,rw and.comm, exact(L1Lb p c Hc Hp Hpc),
    apply and.intro,exact not_modeq_list p c Hpc Hp0 Hc,
    have Hco:coprime 1 p:=begin apply coprime.symm,rw[prime.coprime_iff_not_dvd Hp],exact prime.not_dvd_one Hp, end, exact not_modeq_list p 1 Hco Hp0 (dec_trivial:1>0),
    cases c,have:=coprime.gcd_eq_one Hpc,exfalso,revert this,simp[gcd],unfold prime at Hp,intro,rw this at Hp,revert Hp,simp [(dec_trivial:¬1≥2)],exact dec_trivial,

    have Hp3:(p-1)<p:= nat.sub_lt_self (lt_trans (dec_trivial:0<1) (prime.gt_one Hp)) (dec_trivial:1>0), have:=prime_not_dvd_fact p (p-1) Hp3 Hp, rw ←prime.coprime_iff_not_dvd Hp at this, exact coprime.symm this,
end

theorem fermats_little_theorem : ∀ b p:ℕ,prime p→b^p ≡ b [MOD p]:=begin
    assume b p,cases decidable.em (p ∣ b) with A A,
    have H:∀x y z:ℕ, 1≤z→x ∣ y → y^z ≡ 0 [MOD x] :=begin
        intros x y z H H1,
        induction z with z1 Hi,exfalso,revert H,exact dec_trivial,
        cases z1 with z2,simp,rwa nat.modeq.modeq_zero_iff,
        rw nat.pow_succ,have H2:= Hi dec_trivial,rw nat.modeq.modeq_zero_iff at H2,
        rw nat.modeq.modeq_zero_iff, exact dvd_mul_of_dvd_left H2 _,
    end,intro H1,have :1≤ p:=by {unfold nat.prime at H1,exact le_trans (dec_trivial:1≤2) (and.left H1)},
    have := H p b p this A,rw ←modeq.modeq_zero_iff at A,have A:= modeq.symm A,exact modeq.trans this A,
    assume Hp,rw ←prime.coprime_iff_not_dvd Hp at A,have Hp0:p>0:=begin unfold prime at Hp, exact lt_of_lt_of_le (dec_trivial:0<2) (Hp.left) end,
    suffices :b^(p-1)≡ 1 [MOD p],have h:= modeq.modeq_mul this (modeq.refl b),rwa [one_mul,←pow_succ,←succ_sub,succ_sub_one ]at h,
    exact le_trans (dec_trivial:1≤2) (prime.ge_two Hp),apply fermats_little_theorem1 b p Hp (coprime.symm A),   
end

end nat 