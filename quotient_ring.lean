import linear_algebra.quotient_module

open set

variables {α : Type*} [ring α]

class is_ideal (I : set α) extends is_submodule I : Prop

class prime_ideal (I : set α) extends is_ideal I :=
( prime : ∀ {x y}, x * y ∈ I → x ∈ I ∨ y ∈ I )

class maximal_ideal (I : set α) extends is_ideal I :=
( maximal : ∀ {J}, J ⊂ univ → I ⊂ J → ¬is_ideal J )

instance maximal_ideal.prime_ideal (I : set α) [m : maximal_ideal I] : prime_ideal I :=
{ prime := λ x y hxy, classical.by_contradiction (λ h, begin end),
  ..m }