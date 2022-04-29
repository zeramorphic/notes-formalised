import tactic.basic

universe u

-- 1.2 Basic notion
-- Much of these definitions are copied from mathlib.

-- Semigroups

@[protect_proj, ancestor has_mul, ext]
class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))

@[protect_proj, ancestor has_add, ext]
class add_semigroup (G : Type u) extends has_add G :=
(add_assoc : ∀ a b c : G, a + b + c = a + (b + c))

attribute [to_additive] semigroup

section semigroup
variables {G : Type u} [semigroup G]

@[no_rsimp, to_additive]
lemma mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
semigroup.mul_assoc

@[to_additive]
instance semigroup.to_is_associative : is_associative G (*) :=
⟨mul_assoc⟩

end semigroup

-- Monoids

@[ancestor semigroup has_one]
class monoid (M : Type u) extends semigroup M, has_one M :=
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)

@[ancestor add_semigroup has_zero]
class add_monoid (M : Type u) extends add_semigroup M, has_zero M :=
(one_add : ∀ (a : M), 0 + a = a)
(add_one : ∀ (a : M), a + 0 = a)

attribute [to_additive] monoid

section monoid
variables {M : Type u} [monoid M]

@[to_additive]
instance monoid.to_is_left_id : is_left_id M (*) 1 :=
⟨ monoid.one_mul ⟩

@[to_additive]
instance monoid.to_is_right_id : is_right_id M (*) 1 :=
⟨ monoid.mul_one ⟩

end monoid

-- Groups

@[ancestor monoid has_inv]
class group (G : Type u) extends monoid G, has_inv G :=
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)
(mul_right_inv : ∀ (a : G), a * a⁻¹ = 1)

@[ancestor add_monoid has_neg]
class add_group (G : Type u) extends add_monoid G, has_neg G :=
(mul_left_inv : ∀ (a : G), -a + a = 0)
(mul_right_inv : ∀ (a : G), a + -a = 0)

attribute [to_additive] group

section group
variables {G : Type u} [group G] {a b c : G}

@[simp, to_additive]
lemma mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
group.mul_left_inv

@[to_additive] lemma inv_mul_self (a : G) : a⁻¹ * a = 1 := mul_left_inv a

@[simp, to_additive]
lemma mul_right_inv : ∀ a : G, a * a⁻¹ = 1 :=
group.mul_right_inv

@[to_additive] lemma mul_inv_self (a : G) : a * a⁻¹ = 1 := mul_right_inv a

end group

-- 1.3 Examples

-- (i) trivial group
instance : has_mul unit := ⟨λ x y, ()⟩
instance : semigroup unit := by {split, simp}
instance : has_one unit := ⟨()⟩
instance : monoid unit := by {split; simp}
instance : has_inv unit := ⟨λ x, ()⟩
instance : group unit := by {split; simp}

-- (iii) (ℤ, +)
instance : add_semigroup ℤ := ⟨int.add_assoc⟩
instance : add_monoid ℤ := ⟨int.zero_add, int.add_zero⟩
instance : add_group ℤ := ⟨int.add_left_neg, int.add_right_neg⟩

-- (iv) TODO: rationals, reals, complex numbers
