import data.mv_polynomial ring_theory.ideal_operations ring_theory.adjoin_root
import ring_theory.integral_closure

namespace adjoin_root
variables {α : Type*} [comm_ring α] {f : polynomial α}
open polynomial ideal

lemma coe_injective_of_degree_pos_of_monic (hf : 0 < degree f) (hm : monic f) :
  function.injective (coe : α → adjoin_root f) :=
λ x y hxy,
begin
  rcases mem_span_singleton.1 (ideal.quotient.eq.1 hxy) with ⟨g, hg⟩,
  classical,
  by_cases hg0 : g = 0,
  { rwa [hg0, mul_zero, sub_eq_zero, C_inj] at hg },
  { have hlc : leading_coeff f * leading_coeff g ≠ 0,
    { rwa [monic.def.1 hm, one_mul, ne.def, leading_coeff_eq_zero] },
    exact false.elim (not_le_of_gt hf $
      calc degree f = nat_degree f : degree_eq_nat_degree (λ hf0, by simp * at *)
      ... ≤ nat_degree f + nat_degree g : with_bot.coe_le_coe.2 (nat.le_add_right _ _)
      ... = 0 : by rw [← with_bot.coe_add, ← nat_degree_mul_eq' hlc, ← hg, ← C_sub, nat_degree_C,
        with_bot.coe_zero]) }
end
end adjoin_root
#print ideal.leading_coeff
namespace ideal
variables {R : Type*} [comm_ring R]

@[simp] lemma span_empty : (span ∅ : ideal R) = ⊥ :=
submodule.span_empty

lemma quotient.mk_eq_zero {I : ideal R} {x : R} : ideal.quotient.mk I x = 0 ↔ x ∈ I :=
submodule.quotient.mk_eq_zero _

lemma ext_iff {I J : ideal R} : I = J ↔ (∀ x, x ∈ I ↔ x ∈ J) :=
⟨λ h _, h ▸ iff.rfl, ideal.ext⟩

end ideal

namespace mv_polynomial

lemma C_inj {R σ : Type*} [comm_semiring R] {x y : R} : (C x : mv_polynomial σ R) = C y ↔ x = y :=
sorry

noncomputable instance {R σ : Type*} [nonzero_comm_semiring R] :
  nonzero_comm_semiring (mv_polynomial σ R) :=
{ zero_ne_one := sorry,
  ..show comm_semiring (mv_polynomial σ R), by apply_instance }


end mv_polynomial

namespace polynomial

open ideal set
open_locale classical
end polynomial

open mv_polynomial ideal
universes u v
variables (K : Type u) [discrete_field K]
noncomputable theory

section name
variables {α : Type*} {β : Type*} {σ : Type*} [comm_ring α] [comm_ring β]

def mname (i : σ) (p : polynomial α) : mv_polynomial σ α :=
p.eval₂ C (X i)

@[simp] lemma mname_one (i : σ)  :
  mname i (1 : polynomial α) = 1 :=
by simp [mname]

@[simp] lemma mname_zero (i : σ)  :
  mname i (0 : polynomial α) = 0 :=
by simp [mname]

@[simp] lemma mname_add (i : σ) (p q : polynomial α) :
  mname i (p + q) =  mname i p + mname i q :=
by simp [mname]

@[simp] lemma mname_mul (i : σ) (p q : polynomial α) :
  mname i (p * q) =  mname i p * mname i q :=
by simp [mname]

@[simp] lemma mname_pow (i : σ) (p : polynomial α) (n : ℕ) :
  mname i (p ^ n) =  mname i p ^ n :=
by induction n; simp [pow_succ, *]

@[simp] lemma mname_sub (i : σ) (p q : polynomial α) :
  mname i (p - q) =  mname i p - mname i q :=
by simp [mname]

@[simp] lemma mname_neg (i : σ) (p : polynomial α) :
  mname i (-p) = -mname i p :=
by simp [mname]

@[simp] lemma mname_C (i : σ) (a : α) :
  mname i (polynomial.C a) = C a :=
by simp [mname]

@[simp] lemma mname_X (i : σ) :
  mname i (polynomial.X : polynomial α) = X i :=
by simp [mname]

@[simp] lemma eval₂_mname (i : σ) (f : α → β) [is_semiring_hom f] (s : σ → β) (p : polynomial α) :
  eval₂ f s (mname i p) = polynomial.eval₂ f (s i) p :=
polynomial.induction_on p
  (λ a, by simp)
  (by simp {contextual := tt})
  (by simp [pow_succ', (mul_assoc _ _ _).symm] {contextual := tt})

end name


@[reducible] def posd : Type u := {p : polynomial K // 0 < p.degree ∧ p.monic}

@[reducible] def pac : Type u :=
mv_polynomial (posd K) K

variable {K}

namespace pac
variable (K)
def relt (s : set (posd K)) : set (pac K) :=
(λ p : posd K, p.1.eval₂ C (X p)) '' s

end pac
open pac

set_option class.instance_max_depth 50

@[instance, priority 100000] instance :
  comm_ring (pac K) := mv_polynomial.comm_ring

def F1 (s : set (posd K)) : K →+* ideal.quotient (span (relt K s)) :=
(ring_hom.of (ideal.quotient.mk (span (relt K s)))).comp (ring_hom.of (C : K → pac K))

def F2 (s : set (posd K)) (p : posd K) : K →+* adjoin_root (p.1.map (F1 s)) :=
(ring_hom.of coe).comp $ (ring_hom.of $ ideal.quotient.mk (span (relt K s))).comp $
  ring_hom.of (C : K → pac K)

open_locale classical

lemma isom2 (s : set (posd K)) (p : posd K) (hps : p ∉ s) :
  ideal.quotient (span (relt K (insert p s))) →+* adjoin_root (p.1.map (F1 s)) :=
ring_hom.of $ ideal.quotient.lift _
  (eval₂ (F2 s p) (λ q, if q ∈ s
    then (↑(ideal.quotient.mk (span (relt K s)) (X q : pac K)) : adjoin_root _)
      else if q = p then adjoin_root.root
      else 0))
  begin
    assume x hx,
    refine submodule.span_induction hx _ (by simp) (by simp {contextual := tt})
      (by simp {contextual := tt}),
    assume x hx,
    rcases hx with ⟨q, hq, rfl⟩,
    { rcases hq with rfl | hq,
      { dsimp only [F2, F1],
        rw [← mname, ← adjoin_root.eval₂_root, eval₂_mname, if_pos rfl,
          if_neg hps, polynomial.eval₂_map],
        refl },
      { dsimp only,
        have : ideal.quotient.mk (span (relt K s)) (mname q q) = 0,
        { rw [ideal.quotient.mk_eq_zero],
          exact subset_span (set.mem_image_of_mem _ hq) },
        erw [← mname, eval₂_mname, if_pos hq,
          ← is_ring_hom.map_zero (coe : ideal.quotient (span (relt K s)) →
            adjoin_root (p.1.map (F1 s))), ← this, mname, F2],
        exact eq.symm (polynomial.hom_eval₂ (q : polynomial K) _
          (ring_hom.comp (ring_hom.of (coe : ideal.quotient (span (relt K s)) →
            adjoin_root (p.1.map (F1 s))))
          (ring_hom.of (ideal.quotient.mk (span (relt K s))))) (X q)) } }
  end

open polynomial

lemma map1 (s : set (posd K)) (p : posd K)
  (h01' : (0 :  ideal.quotient (span (relt K s))) ≠ 1) :
  (0 : adjoin_root (p.1.map (F1 s))) ≠ 1 :=
λ h01,
  by rw [← is_ring_hom.map_zero (coe : ideal.quotient (span (relt K s)) →
    adjoin_root (p.1.map (F1 s))),
   ← is_ring_hom.map_one (coe : ideal.quotient (span (relt K s)) →
    adjoin_root (p.1.map (F1 s)))] at h01; exact
h01' (adjoin_root.coe_injective_of_degree_pos_of_monic
  begin
    refine lt_of_not_ge' _,
    rw [degree_le_zero_iff],
    assume h,
    have : (p.1.map (F1 s)).coeff p.1.nat_degree =
      (polynomial.C ((p.1.map (F1 s)).coeff 0)).coeff p.1.nat_degree, { rw ← h },
    have h0 : nat_degree p.1 ≠ 0,
    { rw [← nat.pos_iff_ne_zero, ← with_bot.coe_lt_coe],
      exact lt_of_lt_of_le p.2.1 degree_le_nat_degree },
    rw [polynomial.coeff_C, polynomial.coeff_map, ← polynomial.leading_coeff,
      monic.def.1 p.2.2, ring_hom.map_one, if_neg h0] at this,
    exact h01'.symm this
  end
  (monic_map _ p.2.2)
  h01).

lemma ne_top_aux (s : finset (posd K)) : span (relt K ↑s) ≠ ⊤ :=
finset.induction_on s
  (by simp [ne_top_iff_one, relt, ideal.ext_iff, classical.not_forall]; exact ⟨1, by simp⟩)
  (λ p s hps ih,
    have (0 : ideal.quotient (span (relt K ↑s))) ≠ 1,
      from ne.symm $ mt (ideal.quotient.mk_eq_zero).1 ((ne_top_iff_one _).1 ih),
    have (0 :  adjoin_root (p.1.map (F1 (↑s : set (posd K))))) ≠ 1,
      from map1 ↑s p this,
    have (0 : ideal.quotient (span (relt K (insert p ↑s)))) ≠ 1,
      from λ h, this $ by rw [← ring_hom.map_zero (isom2 ↑s p hps), h, ring_hom.map_one],
    by rw [finset.coe_insert, ne_top_iff_one, ← ideal.quotient.mk_eq_zero, eq_comm];
      exact this)

lemma ne_top : span (relt K ⊤) ≠ ⊤ :=
(ne_top_iff_one _).2 $ λ h : 1 ∈ span (relt K ⊤),
have hs : ∃ s : finset (posd K), (1 : pac K) ∈ span (relt K ↑s),
  from submodule.span_induction h
    (by rintros x ⟨p, hp, rfl⟩; exact ⟨{p}, subset_span (by simp [relt])⟩)
    ⟨∅, by simp⟩
    (by rintros x y ⟨s, hs⟩ ⟨t, ht⟩;
      exact ⟨s ∪ t, ideal.add_mem _ (span_mono (by simp [relt, set.image_union]) hs)
                                    (span_mono (by simp [relt, set.image_union]) ht)⟩)
    (by rintros a x ⟨s, hs⟩; exact ⟨s, ideal.mul_mem_left _ hs⟩),
by cases hs with s hs;
  exact ne_top_aux s ((not_iff_not.1 (ne_top_iff_one _)).2 hs)

variable (K)
def big_ideal : ideal (pac K) :=
classical.some (exists_le_maximal (span (relt K ⊤)) ne_top)

def K1 : Type u :=
ideal.quotient (@big_ideal K _)

instance : discrete_field (K1 K) :=
@ideal.quotient.field _ _ _
  (classical.some_spec (exists_le_maximal (span (relt K ⊤)) ne_top)).1

variables {K}

def of : K → K1 K := ideal.quotient.mk _ ∘ mv_polynomial.C

instance of.is_ring_hom : is_ring_hom (@of K _) := is_ring_hom.comp _ _

instance : algebra K (K1 K) := algebra.of_ring_hom of of.is_ring_hom

lemma algebra_map_eq_of : algebra_map (K1 K) = of := rfl

lemma aeval_posd {f : posd K} : (polynomial.aeval K (K1 K)
  (ideal.quotient.mk (big_ideal K) (X f)) :
    polynomial K → K1 K) f.1 = 0 :=
begin
  rw [polynomial.aeval_def, algebra_map_eq_of, of,
    ← hom_eval₂ _ mv_polynomial.C (ideal.quotient.mk (big_ideal K)), ← mname],
  exact ideal.quotient.mk_eq_zero.2
    ((classical.some_spec (exists_le_maximal (span (relt K ⊤)) ne_top)).2
      (subset_span (set.mem_image_of_mem _ (set.mem_univ _))))
end

lemma is_integral_aux {f : posd K} : @is_integral K (K1 K) _ _ _
  (ideal.quotient.mk _ (X f) : K1 K) :=
⟨f, f.2.2, aeval_posd⟩

lemma mem_integral_closure (x : K1 K) : is_integral K x :=
quotient.induction_on' x $ λ x,
  show ideal.quotient.mk _ x ∈ integral_closure K (K1 K),
  from mv_polynomial.induction_on x
    (λ k, is_integral_algebra_map)
    sorry -- subalgebra.add_mem
    (λ x p, sorry)
