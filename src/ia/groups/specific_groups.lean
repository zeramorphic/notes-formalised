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
: H.carrier × K.carrier ≅ G :=
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

end notes
