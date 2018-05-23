import linear_algebra.basic

variables {α : Type*} {β : Type*} {γ : Type*} [hα : field α] [hβ : vector_space α β]
[hγ : vector_space α γ]
include hα hβ hγ

def is_eigen (f : β → β) (hf : is_linear_map f) (v : β) (e : α) : Prop := ∀ a, f (a • v) = e • v

#print acc
#print is_basis
#print bool
#print nat.no_confusion_type
#print nat.no_confusion