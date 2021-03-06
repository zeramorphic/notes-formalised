import ia.groups.hom
import data.nat.modeq
import set_theory.cardinal.finite

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

lemma cyclic_group.coe_eq_val {n : ℕ} {n_pos : 0 < n} (a : cyclic_group n n_pos) :
↑a = a.val := rfl

lemma cyclic_group.eq_of_modeq {n : ℕ} {n_pos : 0 < n} {a b : cyclic_group n n_pos}
(h : a ≡ b [MOD n]) : a = b :=
begin
  ext,
  unfold nat.modeq at h,
  rw [ cyclic_group.coe_eq_val,
    cyclic_group.coe_eq_val,
    nat.mod_eq_of_lt a.property,
    nat.mod_eq_of_lt b.property ] at h,
  exact h
end

@[simp]
lemma cyclic_group.add_def {n : ℕ} {n_pos : 0 < n} (a b : cyclic_group n n_pos) :
(a + b).val = (a.val + b.val) % n := rfl

lemma cyclic_group.val_eq_mod_of_mod_eq {n : ℕ} {n_pos : 0 < n} {a : cyclic_group n n_pos} {b : ℕ}
(h : a.val ≡ b [MOD n]) : a.val = b % n :=
begin
  unfold nat.modeq at h,
  rw ← h,
  symmetry,
  apply nat.mod_eq_of_lt,
  exact a.property
end

lemma cyclic_group.val_eq_of_lt_of_mod_eq {n : ℕ} {n_pos : 0 < n} {a : cyclic_group n n_pos} {b : ℕ}
(h : a.val ≡ b [MOD n]) (hlt : b < n) : a.val = b :=
begin
  rw ← nat.mod_eq_of_lt hlt,
  exact cyclic_group.val_eq_mod_of_mod_eq h
end

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

instance {n : ℕ} {n_pos : 0 < n} : has_one (cyclic_group n n_pos) := ⟨⟨1 % n, nat.mod_lt 1 n_pos⟩⟩

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
⟪{x}⟫ = (subgroup.univ : subgroup G)

@[to_additive]
def is_mul_cyclic (G : Type*) [group G] : Type* :=
Σ' (x : G), is_mul_generator x

@[to_additive]
lemma is_mul_generator_def [group G] {x : G} : is_mul_generator x ↔ ⟪{x}⟫ = (subgroup.univ : subgroup G) := iff.rfl

@[simp, to_additive]
lemma mem_of_is_mul_generator [group G] {x : G} (h : is_mul_generator x) (y : G) : y ∈ (⟪{x}⟫ : subgroup G) :=
begin
  rw is_mul_generator_def at h,
  rw h,
  simp
end

@[simp, to_additive]
lemma mem_of_is_mul_cyclic [group G] (h : is_mul_cyclic G) (y : G) : y ∈ (⟪{h.fst}⟫ : subgroup G) :=
begin
  apply mem_of_is_mul_generator,
  exact h.snd
end

-- TODO: cyclic_group.is_cyclic

-- The generated subgroup from one element has elements
-- exactly of the form x ^ n for some integer n.
@[to_additive]
lemma singleton_generated_subgroup_elements [group G] (x y : G) :
y ∈ (⟪{x}⟫ : subgroup G) ↔ ∃ (n : ℤ), y = x ^ n :=
begin
  split,
  { intro h,
    specialize h ((λ n, x ^ n) '' (@set.univ ℤ)),
    simp at h,
    obtain ⟨n, hn⟩ := h 1 (group.pow_one_int x) ⟨_, _, _⟩,
    { exact ⟨n, hn.symm⟩ },
    { rintros a b ⟨c, hc⟩ ⟨d, hd⟩,
      refine ⟨c + d, _⟩,
      rw group.add_int_pow,
      rw hc, rw hd },
    { refine ⟨0, _⟩,
      simp },
    { rintros a ⟨b, hb⟩,
      refine ⟨-b, _⟩,
      rw ← hb,
      rw group.int_pow_neg_eq_inv_pow,
      rw group.inv_int_pow_eq_int_pow_inv } },
  { rintro ⟨n, hn⟩,
    rw hn,
    refine subgroup.int_pow_mem _ _,
    exact subgroup.subseteq_generated_subgroup {x} (set.mem_singleton x) }
end

@[to_additive]
lemma singleton_generated_subgroup_eq [group G] (x : G) :
(⟪{x}⟫ : subgroup G).carrier = set.range (λ (n : ℤ), x ^ n) :=
begin
  ext,
  rw subgroup.mem_carrier,
  rw singleton_generated_subgroup_elements x,
  simp,
  simp_rw eq_comm
end

@[to_additive]
lemma pow_injective_of_order_finite [group G] {x : G} {n : ℕ} (h : group.order x = enat.some n) :
function.injective (λ (m : {k // k < n}), x ^ m.val) :=
begin
  intros a b h₁,
  ext,
  dsimp at h₁,
  rw ← group.pow_int_coe at h₁,
  rw ← group.pow_int_coe at h₁,
  rw ← group.pow_eq_pow_iff_order_dvd_sub h at h₁,
  rw int.dvd_iff_mod_eq_zero at h₁,
  rw ← int.mod_eq_mod_iff_mod_sub_eq_zero at h₁,
  rw int.mod_eq_of_lt at h₁,
  rw int.mod_eq_of_lt at h₁,
  rw ← int.coe_nat_eq_coe_nat_iff,
  exact h₁,
  { rw ← int.of_nat_eq_coe, exact int.zero_le_of_nat _ },
  { exact int.coe_nat_lt_coe_nat_of_lt b.property },
  { rw ← int.of_nat_eq_coe, exact int.zero_le_of_nat _ },
  { exact int.coe_nat_lt_coe_nat_of_lt a.property }
end

@[to_additive]
lemma singleton_generated_subgroup_eq_finite [group G] {x : G} {n : ℕ} (h : group.order x = enat.some n) :
(⟪{x}⟫.carrier : set G) = finset.map ⟨(λ (m : {k : ℕ // k < n}), x ^ m.val), pow_injective_of_order_finite h⟩ (finset.fin_range n) :=
begin
  rw singleton_generated_subgroup_eq,
  ext y,
  simp,
  split,
  { rintro ⟨p, hp⟩,
    refine ⟨int.nat_mod p n, _, _⟩,
    { unfold int.nat_mod,
      rw ← int.to_nat_coe_nat n,
      rw int.to_nat_lt_to_nat,
      simp,
      apply int.mod_lt_of_pos,
      exact group.zero_lt_order_int h,
      exact group.zero_lt_order_int h, },
    { rw ← hp,
      rw ← group.pow_int_coe,
      rw ← group.pow_eq_pow_iff_order_dvd_sub h,
      rw int.dvd_iff_mod_eq_zero,
      rw ← int.mod_eq_mod_iff_mod_sub_eq_zero,
      unfold int.nat_mod,
      rw int.to_nat_of_nonneg _,
      { simp },
      apply int.mod_nonneg,
      exact (group.zero_ne_order_int h).symm } },
  { rintro ⟨p, hp₁, hp₂⟩,
    refine ⟨↑p, _⟩,
    rw ← hp₂,
    simp }
end

@[to_additive]
lemma exists_eq_pow_of_mul_cyclic [group G] (hcyclic : is_mul_cyclic G) (x : G) :
∃ (n : ℤ), x = hcyclic.fst ^ n :=
begin
  rw ← singleton_generated_subgroup_elements hcyclic.fst x,
  simp
end

@[to_additive]
theorem singleton_generated_subgroup_card_eq_order [group G] (x : G) :
enat.card (⟪{x}⟫.carrier : set G) = group.order x :=
begin
  rw singleton_generated_subgroup_eq,
  simp,
  by_cases order x = ⊤,
  { rw h,
    haveI : infinite (set.range (λ (n : ℤ), x ^ n)),
    { rw set.infinite_coe_iff,
      apply set.infinite_range_of_injective,
      intros a b hab,
      simp at hab,
      rw group.pow_eq_pow_iff_eq_of_order_infinite _ _ _ h at hab,
      exact hab },
    apply enat.card_eq_top_of_infinite },
  { unfold order at h,
    have exists_order := mt (enat.find_eq_top_iff _).mpr h,
    push_neg at exists_order,
    have order_dom := enat.find_dom _ exists_order,
    let o := (order x).get order_dom,
    rw ← singleton_generated_subgroup_eq,
    have order_rw : order x = enat.some o := by rw ← enat.get_eq_iff_eq_some,
    rw singleton_generated_subgroup_eq_finite order_rw,
    rw enat.card_eq_coe_fintype_card,
    rw order_rw,
    rw enat.some_eq_coe,
    simp }
end

@[to_additive]
lemma mul_generator_order_eq_card_of_finite [group G] [fintype G] (h : is_mul_cyclic G) :
group.order_of_finite h.fst = nat.card G :=
begin
  unfold group.order_of_finite,
  have := singleton_generated_subgroup_card_eq_order h.fst,
  have h_snd : ⟪{h.fst}⟫ = (subgroup.univ : subgroup G) := h.snd,
  rw h_snd at this,
  simp at this ⊢,
  rw enat.get_eq_iff_eq_coe,
  rw ← this,
  simp,
  rw fintype.card_eq,
  refine ⟨_⟩,
  apply equiv.subtype_univ_equiv,
  simp
end

@[to_additive]
lemma mul_generator_infinite_order_of_infinite [group G] [infinite G] (h : is_mul_cyclic G) :
group.order h.fst = ⊤ :=
begin
  unfold order,
  rw enat.find_eq_top_iff,
  intro n,
  apply nat.case_strong_induction_on n; clear n,
  { simp },
  rintros n hn₁ hn₂,
  have lt_find := enat.lt_find (λ m, 0 < m ∧ h.fst ^ m = 1) n hn₁,
  have find_le := enat.find_le (λ m, 0 < m ∧ h.fst ^ m = 1) n.succ hn₂,
  have eq_order : ↑(n.succ) = enat.find (λ m, 0 < m ∧ h.fst ^ m = 1),
  { have := enat.add_one_le_of_lt lt_find,
    simp at find_le ⊢,
    exact le_antisymm this find_le },
  change ↑(n.succ) = group.order h.fst at eq_order,
  rw ← enat.some_eq_coe at eq_order,
  have := singleton_generated_subgroup_eq_finite eq_order.symm,
  have h_snd : ⟪{h.fst}⟫ = _ := h.snd,
  rw h_snd at this,
  refine @fintype.false G _ (set.fintype_of_univ_finite _),
  rw subgroup.univ_def at this,
  rw this,
  simp,
  refine set.finite.image _ _,
  rw finset.coe_fin_range,
  exact @set.finite_univ _ (fin.fintype _)
end

@[to_additive]
theorem mul_generator_order_eq_group_order [group G] (h : is_mul_cyclic G) :
group.order h.fst = enat.card G :=
begin
  by_cases htop : enat.card G = ⊤,
  { rw htop,
    haveI : infinite G,
    { split, intro h,
      rw @enat.card_eq_coe_fintype_card _ h at htop,
      exact enat.coe_ne_top _ htop },
    apply mul_generator_infinite_order_of_infinite },
  { haveI : fintype G,
    { apply fintype_of_not_infinite,
      intro inf,
      exact htop (@enat.card_eq_top_of_infinite _ inf) },
    change _ ≠ ⊤ at htop,
    rw enat.ne_top_iff at htop,
    obtain ⟨n, hn⟩ := htop,
    rw hn,
    rw enat.card_eq_coe_fintype_card at hn,
    have := mul_generator_order_eq_card_of_finite h,
    rw nat.card_eq_fintype_card at this,
    rw ← this at hn,
    rw ← hn,
    unfold order_of_finite,
    simp }
end

noncomputable def iso_cyclic_of_is_cyclic_of_finite [add_group G] [fintype G] (h : is_add_cyclic G) :
cyclic_group (add_group.order_of_finite h.fst) (add_group.zero_lt_order_finite h.fst) ≅+ G :=
begin
  let x := h.fst,
  let n := add_group.order_of_finite h.fst,
  refine ⟨⟨λ k, k.val • x, _⟩, _, _⟩,
  { intros a b,
    rw cyclic_group.add_def,
    rw ← add_group.add_nat_nsmul,
    rw ← add_group.neg_neg ((a.val + b.val) • x),
    apply add_group.eq_neg_of_add_eq_zero,
    rw ← add_group.nsmul_int_coe,
    rw ← add_group.nsmul_int_coe,
    rw add_group.neg_nsmul_eq_nsmul_neg,
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
    rw add_group.eq_zero_of_nsmul_order,
    { apply add_group.nsmul_zero_int },
    { rw add_group.order_eq_some_order_of_finite } },
  { intros a b g,
    dsimp at g,
    refine cyclic_group.eq_of_modeq _,
    apply nat.modeq_of_dvd,
    refine (add_group.eq_zero_iff_int_nsmul_order_dvd (add_group.order_eq_some_order_of_finite x)).mpr _,
    rw add_group.sub_int_nsmul,
    simp,
    rw cyclic_group.coe_eq_val,
    rw cyclic_group.coe_eq_val,
    rw g,
    simp },
  { intro y,
    dsimp,
    obtain ⟨k, hk⟩ := exists_eq_nsmul_of_add_cyclic h y,
    have : y = (int.to_nat (k % n)) • h.fst,
    { rw hk,
      apply add_group.eq_of_add_neg_eq_zero,
      rw ← add_group.nsmul_int_coe,
      rw add_group.neg_nsmul_eq_nsmul_neg,
      rw ← add_group.add_int_nsmul,
      rw ← add_group.eq_zero_iff_int_nsmul_order_dvd (add_group.order_eq_some_order_of_finite x),
      change ↑n ∣ k + -↑((k % ↑n).to_nat),
      rw int.dvd_iff_mod_eq_zero,
      rw ← int.sub_eq_add_neg,
      rw int.sub_mod,
      rw int.to_nat_of_nonneg,
      simp,
      apply int.mod_nonneg,
      exact (add_group.zero_ne_order_finite_int x).symm },
    refine ⟨⟨int.to_nat (k % n), _⟩, _⟩,
    { apply int.lt_of_coe_nat_lt_coe_nat,
      rw int.to_nat_of_nonneg,
      { apply int.mod_lt_of_pos,
        exact add_group.zero_lt_order_finite_int x },
      { apply int.mod_nonneg,
        exact (add_group.zero_ne_order_finite_int x).symm } },
    rw this }
end

-- Infinite cyclic groups

def iso_int_of_is_cyclic_of_infinite [add_group G] [infinite G] (h : is_add_cyclic G) : ℤ ≅+ G :=
begin
  let x := h.fst,
  refine ⟨⟨(• x), _⟩, _, _⟩,
  { intros a b,
    rw add_group.add_int_nsmul },
  { intros a b hab,
    simp at hab,
    have := add_generator_infinite_order_of_infinite h,
    have := add_group.nsmul_eq_nsmul_iff_eq_of_infinite_order this a b,
    exact this.mp hab },
  { intro y,
    simp,
    have := singleton_generated_add_subgroup_elements x y,
    have h_snd : _ = _ := h.snd,
    rw h_snd at this,
    simp at this,
    obtain ⟨n, hn⟩ := this,
    refine ⟨n, hn.symm⟩ }
end

theorem iso_cyclic_or_int_of_is_add_cyclic [add_group G] (h : is_add_cyclic G) :
(∃ n n_pos, cyclic_group n n_pos ∃≅+ G) ∨ (ℤ ∃≅+ G) :=
begin
  rcases fintype_or_infinite G,
  { left,
    haveI := val,
    obtain ⟨x, hx⟩ := h,
    refine ⟨add_group.order_of_finite x, add_group.zero_lt_order_finite _, _⟩,
    split,
    apply iso_cyclic_of_is_cyclic_of_finite ⟨x, hx⟩ },
  { right,
    split,
    apply @iso_int_of_is_cyclic_of_infinite _ _ val h },
end

end notes
