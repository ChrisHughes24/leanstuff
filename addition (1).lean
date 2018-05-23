inductive xnat
| zero : xnat
| succ : xnat → xnat
open xnat
definition one := succ zero
definition two := succ one
definition add :xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (add n p)
notation a + b := add a b
theorem one_add_one_equals_two : one + one = two :=
    begin
        unfold two,
        unfold one,
        unfold add,
    end
theorem add_zerox (n:xnat): n+zero=n:=
    begin
        unfold add,
    end
theorem zero_addx (n:xnat):zero+n=n:=
    begin
        induction n with k H,
        unfold add,
        unfold add,
        rw[H],
    end
theorem add_assocx (a b c:xnat):(a+b)+c=a+(b+c):=
    begin
        induction c with k H,
        unfold add,
        unfold add,
        rw[H],
    end
theorem zero_add_eq_ad_zerox (n:xnat) : zero+n=n+zero:=
    begin 
        rw[zero_addx,add_zerox],
    end
theorem add_one_eq_succx (n:xnat) : n + one = succ n:=
    begin
        unfold one add,
    end
theorem one_add_eq_succx (n : xnat) : one+n=succ n:=
    begin
        induction n with k H,
        unfold one add,
        unfold one add,
        rw[←H],
        unfold one,
    end
theorem add_commx (a b:xnat) : a+b = b+a:=
    begin
        induction b with k H,
        rw[zero_add_eq_ad_zerox],
        unfold add,
        rw[H,←add_one_eq_succx,←add_one_eq_succx,add_assocx,add_assocx,add_one_eq_succx,one_add_eq_succx],
    end
theorem eq_iff_succ_eq_succ (a b : xnat) : succ a = succ b ↔ a = b :=
    begin
        split,
        exact succ.inj,
        assume H : a = b,
        rw [H],
    end
theorem add_cancel_right (a b t : xnat) :  a = b ↔ a+t = b+t :=
    begin
        split,
        assume H,
        rw[H],
        induction t with k H,
        rw[add_zerox,add_zerox],
        assume H1,
        exact H1,
        unfold add,
        rw[eq_iff_succ_eq_succ (a+k) (b+k)],
        exact H,
    end
definition mul:xnat→xnat→xnat
| n zero:=zero
| n (succ p):= mul n p + n
notation a * b := mul a b
theorem mul_zerox (a : xnat) : a * zero = zero :=
    begin
        trivial,
    end
theorem zero_mulx (a : xnat) : zero * a = zero :=
    begin
        induction a with k H,
        unfold mul,
        unfold mul add,
        rw[H],
    end
theorem mul_onex (a : xnat) : a * one = a :=
    begin
        unfold one mul,
        rw[zero_addx],
    end
theorem one_mulx (a : xnat) : one * a = a :=
    begin
        induction a with k H,
        unfold mul,
        unfold mul,
        rw[add_one_eq_succx, H],
    end
theorem right_distribx (a b c : xnat) : a * (b + c) = a* b + a * c :=
    begin
        induction c with k H,
        rw[mul_zerox,add_zerox,add_zerox],
        unfold add mul,
        rw[H, add_assocx],
    end
theorem left_distribx (a b c : xnat) : (a + b) * c = a * c + b * c :=
    begin
        induction c with n Hn,
        unfold mul,
        refl,
        rw [←add_one_eq_succx,right_distribx,Hn,right_distribx,right_distribx],
        rw [mul_onex,mul_onex,mul_onex],
        rw [add_assocx,←add_assocx (b*n),add_commx (b*n),←add_assocx,←add_assocx,←add_assocx],
    end
theorem mul_assocx (a b c : xnat) : (a * b) * c = a * (b * c) :=
    begin
        induction c with k H,
        rw[mul_zerox,mul_zerox,mul_zerox],
        unfold mul,
        rw[right_distribx,H]
    end
theorem mul_commx (a b : xnat) : a * b = b * a :=
    begin
        induction b with k H,
        rw[mul_zerox,zero_mulx],
        unfold mul,
        rw[H],
        exact calc k * a + a = k * a + one * a: by rw[one_mulx]
        ...=(k + one) * a: by rw[left_distribx]
        ...=succ k * a: by rw[add_one_eq_succx],
    end
definition lt : xnat → xnat → Prop 
    | zero zero := false
    | (succ m) zero := false
    | zero (succ p) := true 
    | (succ m) (succ p) := lt m p

notation b > a := lt a b 
notation a < b := lt a b

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t :=
    begin
        induction t with n H,
        rw[add_zerox,add_zerox],
        assume H1,
        exact H1,
        unfold add lt, exact H,
    end
theorem inequality_chris1 (a:xnat) :a < succ a:=
    begin
        induction a with k H,
        unfold lt,
        unfold lt, exact H,
    end
theorem inequality_chris2 (a b:xnat): a<a+succ b:=
    begin
        induction a with k H,
        unfold add,
        unfold add lt, rw[←add_one_eq_succx,add_assocx,one_add_eq_succx],
        exact H,
    end
theorem inequality_chris3 (a b:xnat):a<b → a < (succ b):=
    begin
        assume H,


    end
theorem subtraction (a b :xnat) (Hab:a<b): ∃ (c:xnat), a+succ c=b:=
    begin
        induction b with k Hi,
        fapply exists.intro,
        exact zero, unfold add,admit,
        fapply exists.intro,



    end

theorem exists_test : ∃(a:nat), a=a:=
    begin,
       
    end
theorem inequality_A2 (a b c : xnat) : a<b → b<c → a<c :=
    begin
        assume H1 H2,
        have H3 (d e :xnat) (Hab:d<e): ∃ (f:xnat), d+succ f=e:=sorry,
        exists.elim (subtraction a b H1)
        

    end