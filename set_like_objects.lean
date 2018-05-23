Set like object in lean
### lists ###
`list α` is the type of lists of elements of type re finite and ordered, and can contain duplicates. Lists can only contain elements of the same type. 
`[1, 1, 2, 4] ≠ [1, 2, 1, 4]` 
`[1, 2, 1, 4] ≠ [1, 2, 4]`

### multisets ###
`multiset α` is the type of lists of elements of type α. Multisets are finite and can contain duplicates, but are not ordered. They are defined as the quotient of lists over the `perm` equivalence relation. Multisets can only contain elements of the same type.
`{1, 1, 2, 4} = {1, 2, 1, 4}`
`{1, 1, 2, 4} ≠ {1, 2, 4}`

### finsets ###
`finset α` is the type of lists of elements of type α. A finset is contructed from a multiset and a proof that the multiset contains no duplicates. Finsets are finite. Finsets can only contain elements of the same type.

### sets ###
`set α` a set is defined as a predicate, i.e. a function ` α → Prop`. The notation used is ` {n : ℕ | 4 ≤ n}` for the set of naturals greater than 4. Sets can be infinite, and can only contain elements of the same type.

### subtypes ###
A subtype is similar to a set in that it is defined by a predicate. The notation used is `{n : ℕ // 4 ≤ n}` for the type of naturals greater than 4. However, a subtype is a type rather than a set, and the elements the aforementioned subtype do not have type ℕ, they have type {n : ℕ // 4 ≤ n}. This means that addition is not defined on this type, and equality between naturals and this type is also undefined. However it is possible to coerce an element of this subtype back into a natural, in the same way that a natural can be coerced into an integer, and then addition and equality behave as normal (see TPIL, chapter 6.7 for more on coercions). To construct an element of a subtype of α I need an element of α and a proof that it satisfies the predicate.
def x : {n : ℕ // 4 ≤ n} := ⟨4, le_refl 4⟩
lemma four_add_six : ↑x + 6 = 10 := rfl
In the first example 4 is the natural and `le_refl 4` is the proof that 4 ≤ 4

### fintype ###
Fintype – for any finite type α, an object of type `fintype α` is a finset and 
