import tactic.basic
import data.fintype.basic
--import constructions.rat

universe u

-- Keep everything namespaced to avoid name clashes.
namespace notes

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
(zero_add : ∀ (a : M), 0 + a = a)
(add_zero : ∀ (a : M), a + 0 = a)

attribute [to_additive] monoid

section monoid
variables {M : Type u} [monoid M]

@[simp, to_additive]
lemma one_mul : ∀ (a : M), 1 * a = a := monoid.one_mul

@[simp, to_additive]
lemma mul_one : ∀ (a : M), a * 1 = a := monoid.mul_one

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

@[simp, to_additive]
lemma mul_right_inv : ∀ a : G, a * a⁻¹ = 1 :=
group.mul_right_inv

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

-- 1.6 Basic group properties

namespace group

variables {G : Type u} [group G] {a b : G}

@[to_additive]
lemma eq_one_of_left_id (h : ∀ b, a * b = b) : a = 1 :=
begin
  have := h 1,
  rwa mul_one at this,
end

@[to_additive]
lemma eq_one_of_right_id (h : ∀ b, b * a = b) : a = 1 :=
begin
  have := h 1,
  rwa one_mul at this,
end

@[to_additive]
lemma eq_inv_of_mul_eq_one (h : a * b = 1) : a = b⁻¹ :=
begin
  have : a * b * b⁻¹ = 1 * b⁻¹ := by rw h,
  rw one_mul at this,
  rw mul_assoc at this,
  rw mul_right_inv at this,
  rwa mul_one at this,
end

@[to_additive]
lemma mul_inv (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  rw ← eq_inv_of_mul_eq_one,
  rw mul_assoc,
  rw ← mul_assoc a⁻¹,
  simp,
end

@[simp, to_additive]
lemma inv_inv (a : G) : a⁻¹⁻¹ = a :=
begin
  rw ← eq_inv_of_mul_eq_one,
  exact mul_right_inv a,
end

@[simp, to_additive]
lemma one_inv : (1 : G)⁻¹ = 1 :=
begin
  rw ← eq_inv_of_mul_eq_one,
  rw one_mul,
end

end group

@[ancestor group]
class abelian_group (G : Type u) extends group G :=
(mul_comm : ∀ (a b : G), a * b = b * a)

@[ancestor add_group]
class add_abelian_group (G : Type u) extends add_group G :=
(mul_comm : ∀ (a b : G), a + b = b + a)

attribute [to_additive] abelian_group

@[ancestor group]
class finite_group (G : Type u) extends group G :=
(hfinite : fintype G)

@[ancestor add_group]
class finite_add_group (G : Type u) extends add_group G :=
(hfinite : fintype G)

attribute [to_additive] finite_group

@[ancestor group]
class infinite_group (G : Type u) extends group G :=
(hinfinite : infinite G)

@[ancestor add_group]
class infinite_add_group (G : Type u) extends add_group G :=
(hinfinite : infinite G)

attribute [to_additive] infinite_group

namespace finite_group

variables (G : Type u) [finite_group G]

@[to_additive]
def order : ℕ := fintype.sizeof G hfinite

@[to_additive]
instance : has_sizeof G := ⟨order G⟩

end finite_group

-- Subgroups

structure subgroup (G : Type u) [group G] :=
(carrier : set G)
(mul_mem : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier)
(one_mem : (1 : G) ∈ carrier)
(inv_mem : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier)

structure add_subgroup (G : Type u) [add_group G] :=
(carrier : set G)
(mul_mem : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a + b ∈ carrier)
(zero_mem : (0 : G) ∈ carrier)
(neg_mem : ∀ {a : G}, a ∈ carrier → -a ∈ carrier)

attribute [to_additive] subgroup

namespace group

variables (G : Type u) [group G]

@[to_additive]
def trivial_subgroup : subgroup G := {
  carrier := {a | a = 1},
  mul_mem := begin
    dsimp,
    intros a b ha hb,
    rw set.mem_singleton_iff at *,
    rw [ha, hb, one_mul]
  end,
  one_mem := by simp,
  inv_mem := begin
    dsimp,
    intros a ha,
    rw set.mem_singleton_iff at *,
    rw ha,
    exact one_inv,
  end,
}

variables {H : subgroup G}

-- TODO: prove some lemmas about how coercion works with all the other operations
@[to_additive] instance : has_coe H.carrier G := ⟨λ g, ↑g⟩
@[to_additive] lemma coe_def {H: subgroup G} (a : H.carrier)
  : ↑a = a.val := rfl

end group

-- Subgroups are groups

namespace group

variables {G : Type u} [group G] (H : subgroup G)

@[to_additive] instance has_one_of_subgroup : has_one H.carrier :=
⟨⟨1, subgroup.one_mem H⟩⟩

@[simp, to_additive] lemma coe_one : ↑(1 : H.carrier) = (1 : G) := rfl

@[to_additive] instance has_mul_of_subgroup : has_mul H.carrier :=
⟨λ a b, ⟨↑a * ↑b, subgroup.mul_mem H a.property b.property⟩⟩

@[to_additive] lemma coe_eq {a b : H.carrier} (h : (↑a : G) = ↑b) : a = b := by {ext, exact h}
@[to_additive] lemma coe_eq_iff_eq {a b : H.carrier} : a = b ↔ (↑a : G) = ↑b := ⟨congr_arg _, coe_eq H⟩

@[simp, to_additive] lemma coe_mul {a b : H.carrier} : (↑(a * b) : G) = ↑a * ↑b := rfl

@[to_additive] instance semigroup_of_subgroup : semigroup H.carrier :=
⟨λ a b c, begin
  rw coe_eq_iff_eq,
  simp,
  apply mul_assoc
end⟩

@[to_additive] instance monoid_of_subgroup : monoid H.carrier :=
⟨begin
  intro a,
  rw coe_eq_iff_eq,
  simp,
end, begin
  intro a,
  rw coe_eq_iff_eq,
  simp,
end⟩

@[to_additive] instance has_inv_of_subgroup : has_inv H.carrier :=
⟨λ a, ⟨(↑a)⁻¹, by {apply subgroup.inv_mem, simp}⟩⟩

@[simp, to_additive] lemma coe_inv {a : H.carrier} : ↑(a⁻¹) = (↑a : G)⁻¹ := rfl

@[to_additive] instance group_of_subgroup : group H.carrier :=
⟨begin
  intro a,
  rw coe_eq_iff_eq,
  simp,
end, begin
  intro a,
  rw coe_eq_iff_eq,
  simp,
end⟩

end group

-- Results about subgroups

namespace group

variables {G : Type u} [group G]

def is_subgroup (H : set G) := ∃ K : subgroup G, K.carrier = H

lemma is_subgroup_of_mul_inv_mem {H : set G}
(h₁ : H.nonempty) (h₂ : ∀ a b, a ∈ H → b ∈ H → a * b⁻¹ ∈ H) : is_subgroup H :=
begin
  have one_mem : (1 : G) ∈ H,
  { obtain ⟨a, ha⟩ := h₁,
    have := h₂ a a ha ha,
    rwa mul_right_inv at this },
  have inv_mem : ∀ (a : G), a ∈ H → a⁻¹ ∈ H,
  { intros a ha,
    have := h₂ 1 a one_mem ha,
    rwa one_mul at this },
  have mul_mem : ∀ (a b : G), a ∈ H → b ∈ H → a * b ∈ H,
  { intros a b ha hb,
    have := h₂ a b⁻¹ ha _,
    { rwa inv_inv at this },
    exact inv_mem _ hb },
  refine ⟨{carrier := H, mul_mem := mul_mem, one_mem := one_mem, inv_mem := inv_mem}, _⟩,
  dsimp only,
  refl
end

lemma nonempty_of_subgroup (H : subgroup G) : H.carrier.nonempty :=
begin
  refine ⟨1, _⟩,
  apply subgroup.one_mem
end

lemma is_subgroup_iff_mul_inv_mem {H : set G} :
(H.nonempty ∧ ∀ a b, a ∈ H → b ∈ H → a * b⁻¹ ∈ H) ↔ is_subgroup H :=
begin
  split,
  { rintro ⟨h₁, h₂⟩,
    exact is_subgroup_of_mul_inv_mem h₁ h₂ },
  { intro h,
    obtain ⟨K, hK⟩ := h,
    rw ← hK,
    split,
    { apply nonempty_of_subgroup K },
    { intros a b ha hb,
      refine subgroup.mul_mem _ _ _,
      assumption,
      apply subgroup.inv_mem,
      assumption } }
end

end group

end notes
