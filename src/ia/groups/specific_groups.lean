import ia.groups.hom

namespace notes

open group hom

variables {G H K L : Type*}
variables {Φ Ψ Χ : Type*}

-- Direct products of groups

@[to_additive]
instance [semigroup G] [semigroup H] : semigroup (G × H) := {
  mul_assoc := begin
    rintros ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩,
    dsimp,
    rw mul_assoc,
    rw mul_assoc
  end
}

@[to_additive]
instance [monoid G] [monoid H] : monoid (G × H) := {
  one_mul := begin
    rintro ⟨a₁, a₂⟩,
    rw prod.mul_def,
    dsimp,
    rw one_mul,
    rw one_mul
  end,
  mul_one := begin
    rintro ⟨a₁, a₂⟩,
    rw prod.mul_def,
    dsimp,
    rw mul_one,
    rw mul_one
  end
}

@[to_additive]
instance [group G] [group H] : group (G × H) := {
  mul_left_inv := begin
    rintro ⟨a₁, a₂⟩,
    dsimp,
    rw mul_left_inv,
    rw mul_left_inv,
    refl
  end,
  mul_right_inv := begin
    rintro ⟨a₁, a₂⟩,
    dsimp,
    rw mul_right_inv,
    rw mul_right_inv,
    refl
  end
}

def direct_product_theorem [group G] {H K : subgroup G}
(trivial_intersection : H ⊓ K = subgroup.trivial)
(commute : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h)
(span : ∀ g : G, ∃ h ∈ H, ∃ k ∈ K, g = h * k)
: H.carrier × K.carrier ≅* G :=
begin
  let f : H.carrier × K.carrier → G := λ ⟨h, k⟩, h * k,
  let φ : H.carrier × K.carrier →* G := ⟨f, _⟩, swap,
  { rintros ⟨h₁, k₁⟩ ⟨h₂, k₂⟩,
    simp,
    change (h₁ * h₂ : G) * (k₁ * k₂) = (h₁ * k₁) * (h₂ * k₂),
    rw mul_assoc,
    rw ← mul_assoc ↑h₂,
    rw commute ↑h₂,
    { rw [mul_assoc, mul_assoc] },
    { exact set_like.coe_mem h₂ },
    { exact set_like.coe_mem k₁ } },
  refine ⟨φ, _, _⟩,
  { change function.injective φ,
    rw inj_iff_kernel_trivial,
    rw kernel_trivial,
    rintros ⟨h, k⟩ hk,
    change (h : G) * k = 1 at hk,
    have h_mem_K : ↑h ∈ K.carrier := set.mem_of_eq_of_mem
      (eq_inv_of_mul_eq_one hk)
      (subgroup.inv_mem K (subtype.mem k)),
    have : ↑h ∈ H ⊓ K := ⟨subtype.mem h, h_mem_K⟩,
    rw trivial_intersection at this,
    rw subgroup.mem_trivial at this,
    rw this at hk,
    rw one_mul at hk,
    congr',
    { apply subgroup.coe_eq, exact this },
    { apply subgroup.coe_eq, exact hk } },
  { intro g,
    obtain ⟨h, hh, k, hk, hhk⟩ := span g,
    exact ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, hhk.symm⟩ }
end

-- Finite and infinite cyclic groups

@[ext]
structure cyclic_group (n : ℕ) (n_pos : 0 < n) :=
(val : ℕ)
(property : val < n)

instance {n : ℕ} {n_pos : 0 < n} : has_coe (cyclic_group n n_pos) ℕ := ⟨λ x, x.val⟩

instance {n : ℕ} {n_pos : 0 < n} : has_add (cyclic_group n n_pos) :=
⟨λ a b, ⟨(a + b) % n, nat.mod_lt _ n_pos⟩⟩

@[simp]
lemma cyclic_add_def {n : ℕ} {n_pos : 0 < n} (a b : cyclic_group n n_pos) :
(a + b).val = (a.val + b.val) % n := rfl

instance {n : ℕ} {n_pos : 0 < n} : add_semigroup (cyclic_group n n_pos) := {
  add_assoc := begin
    intros a b c,
    ext,
    simp,
    rw nat.add_assoc
  end
}

instance {n : ℕ} {n_pos : 0 < n} : has_zero (cyclic_group n n_pos) :=
⟨⟨0, n_pos⟩⟩

@[simp]
lemma cyclic_zero_def {n : ℕ} {n_pos : 0 < n} : (0 : cyclic_group n n_pos).val = 0 := rfl

instance {n : ℕ} {n_pos : 0 < n} : add_monoid (cyclic_group n n_pos) := {
  zero_add := begin
    intro a,
    ext,
    simp,
    exact nat.mod_eq_of_lt a.property
  end,
  add_zero := begin
    intro a,
    ext,
    simp,
    exact nat.mod_eq_of_lt a.property
  end
}

instance {n : ℕ} {n_pos : 0 < n} : has_neg (cyclic_group n n_pos) :=
⟨λ x, ⟨(n - x) % n, nat.mod_lt _ n_pos⟩⟩

@[simp]
lemma cyclic_neg_def {n : ℕ} {n_pos : 0 < n} (x : cyclic_group n n_pos) :
(-x).val = (n - x) % n := rfl

instance {n : ℕ} {n_pos : 0 < n} : add_group (cyclic_group n n_pos) := {
  add_left_neg := begin
    intro a,
    ext,
    simp,
    change (n - a.val + a.val) % n = 0,
    rw nat.sub_add_cancel (le_of_lt a.property),
    exact nat.mod_self n
  end,
  add_right_neg := begin
    intro a,
    ext,
    simp,
    change (a.val + (n - a.val)) % n = 0,
    rw ← nat.add_sub_assoc (le_of_lt a.property),
    rw nat.add_sub_cancel_left,
    exact nat.mod_self n
  end
}

@[to_additive]
def is_mul_generator [group G] (x : G) : Prop :=
subgroup.generated_subgroup {x} = (subgroup.univ : subgroup G)

@[to_additive]
def is_mul_cyclic (G : Type*) [group G] : Type* :=
Σ' (x : G), is_mul_generator x

#check add_group.add_int_nsmul

theorem iso_cyclic_or_int_of_is_add_cyclic [add_group G] (h : is_add_cyclic G) :
(∃ n n_pos, cyclic_group n n_pos ∃≅+ G) ∨ (ℤ ∃≅+ G) :=
begin
  obtain ⟨x, hx⟩ := h,
  rcases part.eq_none_or_eq_some (add_group.order x) with h₁ | ⟨n, h₂⟩,
  { right,
    sorry },
  { left,
    refine ⟨n, add_group.zero_lt_order h₂, _⟩,
    refine ⟨⟨⟨λ k, k.val • x, _⟩, _, _⟩⟩,
    { intros a b,
      rw cyclic_add_def,
      rw ← add_group.add_nat_nsmul,
      rw ← add_group.neg_neg ((a.val + b.val) • x),
      apply add_group.eq_neg_of_add_eq_zero,
      rw ← add_group.nsmul_int_coe,
      rw ← add_group.nsmul_int_coe,
      rw add_group.neg_nsmul_of_nsmul_neg,
      rw ← add_group.add_int_nsmul,
      have : (n : ℤ) ∣ ↑((a.val + b.val) % n) + -↑(a.val + b.val),
      { apply int.dvd_of_mod_eq_zero,
        simp,
        rw ← int.add_assoc,
        simp },
      obtain ⟨c, hc⟩ := exists_eq_mul_left_of_dvd this,
      rw hc,
      rw int.mul_comm,
      rw ← add_group.nsmul_nsmul,
      rw add_group.nsmul_int_coe,
      rw add_group.eq_zero_of_order_smul,
      {  } } }
end

end notes
