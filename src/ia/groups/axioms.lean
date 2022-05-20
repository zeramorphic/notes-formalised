import tactic.basic
import data.fintype.basic
import data.set_like.basic
import data.nat.enat

universe u

-- Keep everything namespaced to avoid name clashes.
namespace notes

def int.neg_one : -[1+ 0] = -1 := rfl

def int.pred_neg_succ_of_nat (n : ℕ) : -[1+ n + 1] = -[1+ n] - 1 :=
begin
  rw [
    int.neg_succ_of_nat_eq, int.neg_succ_of_nat_eq,
    int.coe_nat_add,
    int.neg_add, int.neg_add, int.neg_add ],
  simp
end

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
(add_left_neg : ∀ (a : G), -a + a = 0)
(add_right_neg : ∀ (a : G), a + -a = 0)

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
instance int.add_semigroup : add_semigroup ℤ := ⟨int.add_assoc⟩
instance int.add_monoid : add_monoid ℤ := ⟨int.zero_add, int.add_zero⟩
instance int.add_group : add_group ℤ := ⟨int.add_left_neg, int.add_right_neg⟩

-- 1.6 Basic group properties

namespace group

variables {G : Type u} [group G]

@[to_additive]
lemma eq_one_of_left_id {a b : G} (h : ∀ b, a * b = b) : a = 1 :=
begin
  have := h 1,
  rwa mul_one at this,
end

@[to_additive]
lemma eq_one_of_right_id {a b : G} (h : ∀ b, b * a = b) : a = 1 :=
begin
  have := h 1,
  rwa one_mul at this,
end

@[to_additive]
lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ :=
begin
  have : a * b * b⁻¹ = 1 * b⁻¹ := by rw h,
  rw one_mul at this,
  rw mul_assoc at this,
  rw mul_right_inv at this,
  rwa mul_one at this,
end

@[to_additive]
lemma mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
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

@[to_additive]
lemma eq_of_mul_inv_eq_one {a b : G} (h : a * b⁻¹ = 1) : a = b :=
begin
  rw ← inv_inv b,
  exact eq_inv_of_mul_eq_one h,
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

namespace subgroup

variables (G : Type u) [group G]

@[to_additive]
def trivial {G : Type u} [group G] : subgroup G := {
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
    exact group.one_inv,
  end,
}

@[simp, to_additive]
lemma trivial_def : (trivial : subgroup G).carrier = {1} := rfl

@[simp, to_additive]
lemma mem_trivial_carrier (x : G) : x ∈ (trivial : subgroup G).carrier ↔ x = 1 := iff.rfl

variables {H : subgroup G}

-- TODO: prove some lemmas about how coercion works with all the other operations
@[to_additive] instance : has_coe H.carrier G := ⟨λ g, ↑g⟩
@[to_additive] lemma coe_def {H: subgroup G} (a : H.carrier)
  : ↑a = a.val := rfl
@[to_additive] instance : has_lift_t (subgroup G) (set G) := ⟨λ K, K.carrier⟩
@[to_additive] lemma lift_t_def (H : subgroup G)
  : ↑H = H.carrier := rfl

end subgroup

-- Subgroups are groups

namespace subgroup

variables {G : Type u} [group G] (H : subgroup G)

@[to_additive]
instance has_one_of_subgroup : has_one H.carrier :=
⟨⟨1, subgroup.one_mem H⟩⟩

@[simp, to_additive]
lemma coe_one : ↑(1 : H.carrier) = (1 : G) := rfl

@[to_additive]
instance has_mul_of_subgroup : has_mul H.carrier :=
⟨λ a b, ⟨↑a * ↑b, subgroup.mul_mem H a.property b.property⟩⟩

@[to_additive]
lemma coe_eq {a b : H.carrier} (h : (↑a : G) = ↑b) : a = b := by {ext, exact h}
@[to_additive]
lemma coe_eq_iff_eq {a b : H.carrier} : a = b ↔ (↑a : G) = ↑b := ⟨congr_arg _, coe_eq H⟩

@[simp, to_additive]
lemma coe_mul {a b : H.carrier} : (↑(a * b) : G) = ↑a * ↑b := rfl

@[to_additive]
instance semigroup_of_subgroup : semigroup H.carrier :=
⟨λ a b c, begin
  rw coe_eq_iff_eq,
  simp,
  apply mul_assoc
end⟩

@[to_additive]
instance monoid_of_subgroup : monoid H.carrier :=
⟨begin
  intro a,
  rw coe_eq_iff_eq,
  simp,
end, begin
  intro a,
  rw coe_eq_iff_eq,
  simp,
end⟩

@[to_additive]
instance has_inv_of_subgroup : has_inv H.carrier :=
⟨λ a, ⟨(↑a)⁻¹, by {apply subgroup.inv_mem, simp}⟩⟩

@[simp, to_additive]
lemma coe_inv {a : H.carrier} : ↑(a⁻¹) = (↑a : G)⁻¹ := rfl

@[to_additive]
instance group_of_subgroup : group H.carrier :=
⟨begin
  intro a,
  rw coe_eq_iff_eq,
  simp,
end, begin
  intro a,
  rw coe_eq_iff_eq,
  simp,
end⟩

end subgroup

-- Results about subgroups

namespace subgroup

variables {G : Type u} [group G]

@[to_additive]
def is_subgroup (H : set G) :=
(∀ {a b : G}, a ∈ H → b ∈ H → a * b ∈ H) ∧
((1 : G) ∈ H) ∧
(∀ {a : G}, a ∈ H → a⁻¹ ∈ H)

@[to_additive]
def mul_mem_of_is_subgroup {H : set G} (h : is_subgroup H) {a b : G}
(ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H :=
begin
  revert a b ha hb,
  exact h.1
end

@[to_additive]
def one_mem_of_is_subgroup {H : set G} (h : is_subgroup H) : (1 : G) ∈ H :=
begin
  exact h.2.1
end

@[to_additive]
def inv_mem_of_is_subgroup {H : set G} (h : is_subgroup H) {a : G}
(ha : a ∈ H) : a⁻¹ ∈ H :=
begin
  revert a ha,
  exact h.2.2
end

@[to_additive]
def subgroup_of_is_subgroup {H : set G} (h : is_subgroup H) : Σ' (K : subgroup G), K.carrier = H :=
⟨⟨H, h.1, h.2.1, h.2.2⟩, rfl⟩

@[to_additive]
lemma is_subgroup_of_subgroup (H : subgroup G) : is_subgroup H.carrier :=
⟨λ a b, mul_mem H, one_mem H, λ a, inv_mem H⟩

@[ext, to_additive]
lemma subgroup_ext {H K : subgroup G} (h : H.carrier = K.carrier) : H = K :=
begin
  induction H,
  induction K,
  congr'
end

@[to_additive]
lemma subgroup_ext_iff {H K : subgroup G} : H.carrier = K.carrier ↔ H = K :=
⟨subgroup_ext, λ h, by congr'⟩

@[to_additive] instance : set_like (subgroup G) G := {
  coe := λ H, H.carrier,
  coe_injective' := begin
    intros H K h,
    exact subgroup_ext h
  end,
}

@[simp, to_additive]
lemma mem_carrier {H : subgroup G} {x : G}
: x ∈ H.carrier ↔ x ∈ H := iff.rfl

@[simp, to_additive]
lemma mem_trivial (x : G) : x ∈ (trivial : subgroup G) ↔ x = 1 := iff.rfl

@[to_additive]
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
    { rwa group.inv_inv at this },
    exact inv_mem _ hb },
  refine ⟨mul_mem, one_mem, inv_mem⟩
end

@[to_additive]
lemma nonempty_of_subgroup (H : subgroup G) : H.carrier.nonempty :=
begin
  refine ⟨1, _⟩,
  apply subgroup.one_mem
end

@[to_additive]
lemma is_subgroup_iff_mul_inv_mem {H : set G} :
(H.nonempty ∧ ∀ a b, a ∈ H → b ∈ H → a * b⁻¹ ∈ H) ↔ is_subgroup H :=
begin
  split,
  { rintro ⟨h₁, h₂⟩,
    exact is_subgroup_of_mul_inv_mem h₁ h₂ },
  { intro h,
    obtain ⟨mul_mem, one_mem, inv_mem⟩ := h,
    --rw ← hK,
    split,
    { apply set.nonempty_of_mem one_mem, },
    { intros a b ha hb,
      refine mul_mem _ _,
      assumption,
      apply inv_mem,
      assumption } }
end

end subgroup

namespace add_subgroup

lemma subgroup_int_of_n_dvd (n : ℤ) : is_add_subgroup {k | (n ∣ k)} :=
begin
  refine is_add_subgroup_of_add_neg_mem _ _,
  { have : (0 : ℤ) ∈ {k | (n ∣ k)},
    { apply int.dvd_of_mod_eq_zero,
      apply int.zero_mod },
    apply set.nonempty_of_mem this },
  { intros a b ha hb,
    dsimp at *,
    rw int.dvd_iff_mod_eq_zero at *,
    rw ← int.sub_eq_add_neg,
    rw int.sub_mod,
    rw ha, rw hb,
    rw sub_zero,
    apply int.zero_mod }
end

-- The converse statement is much more difficult to prove at the moment.

end add_subgroup

-- Lattice of subgroups

namespace subgroup

variables {G : Type u} [group G]

@[to_additive] def le (H K : subgroup G) : Prop := H.carrier ⊆ K.carrier
@[to_additive] instance : has_le (subgroup G) := ⟨le⟩

@[to_additive]
lemma le_def (H K : subgroup G) : H ≤ K ↔ H.carrier ⊆ K.carrier := by refl

@[to_additive]
protected lemma le_refl (H : subgroup G) : H ≤ H := by rw le_def

@[to_additive]
protected lemma le_trans (H K L : subgroup G) (h₁ : H ≤ K) (h₂ : K ≤ L) : H ≤ L :=
begin
  rw le_def at *,
  transitivity K.carrier; assumption
end

@[to_additive] def lt (H K : subgroup G) : Prop := H.carrier ⊂ K.carrier
@[to_additive] instance : has_lt (subgroup G) := ⟨lt⟩

@[to_additive]
lemma lt_def (H K : subgroup G) : H < K ↔ H.carrier ⊂ K.carrier := by refl

@[to_additive]
protected lemma lt_iff_le_not_le (H K : subgroup G) : H < K ↔ H ≤ K ∧ ¬K ≤ H :=
begin
  rw [le_def, le_def, lt_def],
  split,
  { intro h₁,
    split,
    { exact subset_of_ssubset h₁ },
    { intro h₂,
      exact ne_of_ssubset (ssubset_of_ssubset_of_subset h₁ h₂) rfl } },
  { rintro ⟨h₁, h₂⟩,
    refine ssubset_of_subset_of_ne h₁ _,
    intro h₃,
    rw h₃ at h₂,
    exact h₂ subset_rfl }
end

@[to_additive]
protected lemma le_antisymm (H K : subgroup G) (h₁ : H ≤ K) (h₂ : K ≤ H) : H = K :=
begin
  ext,
  rw le_def at *,
  split,
  { intro h,
    exact h₁ h },
  { intro h,
    exact h₂ h }
end

@[to_additive]
def inf (H K : subgroup G) : subgroup G := {
  carrier := ↑H ∩ ↑K,
  mul_mem := λ a b ⟨haH, haK⟩ ⟨hbH, hbK⟩, ⟨mul_mem H haH hbH, mul_mem K haK hbK⟩,
  one_mem := ⟨one_mem H, one_mem K⟩,
  inv_mem := λ a ⟨haH, haK⟩, ⟨inv_mem H haH, inv_mem K haK⟩
}
@[to_additive] instance : has_inf (subgroup G) := ⟨inf⟩

@[to_additive]
lemma inf_def (H K : subgroup G) : (H ⊓ K).carrier = H.carrier ∩ K.carrier := rfl

@[to_additive]
protected lemma inf_le_left (H K : subgroup G) : H ⊓ K ≤ H :=
begin
  rw le_def,
  rw inf_def,
  exact set.inter_subset_left ↑H ↑K
end

@[to_additive]
protected lemma inf_le_right (H K : subgroup G) : H ⊓ K ≤ K :=
begin
  rw le_def,
  rw inf_def,
  exact set.inter_subset_right ↑H ↑K
end

@[to_additive]
protected lemma le_inf (H K L : subgroup G) (hK : H ≤ K) (hL : H ≤ L) : H ≤ K ⊓ L :=
begin
  rw le_def at *,
  rw inf_def,
  refine set.subset_inter _ _; assumption
end

@[to_additive]
def Inf (S : set (subgroup G)) : subgroup G := {
  carrier := ⋂₀ (coe '' S),
  mul_mem := begin
    intros a b ha hb,
    simp at *,
    intros H hH,
    apply mul_mem,
    { exact ha H hH },
    { exact hb H hH }
  end,
  one_mem := begin
    simp,
    intros H hH,
    apply one_mem
  end,
  inv_mem := begin
    intros a ha,
    simp at *,
    intros H hH,
    apply inv_mem,
    exact ha H hH
  end,
}

@[to_additive]
lemma Inf_def (S : set (subgroup G)) : (Inf S).carrier = ⋂₀ (coe '' S) := rfl

@[to_additive]
protected lemma Inf_le (S : set (subgroup G)) (H : subgroup G) (hH : H ∈ S) : Inf S ≤ H :=
begin
  rw le_def,
  rw Inf_def,
  intros a ha,
  simp at ha,
  exact ha H hH
end

@[to_additive]
protected lemma le_Inf (S : set (subgroup G)) (H : subgroup G) (h : ∀ (K : subgroup G), K ∈ S → H ≤ K) : H ≤ Inf S :=
begin
  rw le_def,
  rw Inf_def,
  intros a ha,
  simp,
  intros K hK,
  exact (le_def H K).mp (h K hK) ha
end

@[to_additive]
def generated_subgroup (X : set G) : subgroup G := {
  carrier := ⋂₀ {Y | X ⊆ Y ∧ is_subgroup Y},
  mul_mem := begin
    simp,
    intros a b ha hb Y hY sgY,
    exact mul_mem_of_is_subgroup sgY (ha Y hY sgY) (hb Y hY sgY)
  end,
  one_mem := begin
    simp,
    intros Y hY sgY,
    exact one_mem_of_is_subgroup sgY
  end,
  inv_mem := begin
    simp,
    intros a ha Y hY sgY,
    exact inv_mem_of_is_subgroup sgY (ha Y hY sgY),
  end,
}

@[simp, to_additive]
lemma generated_subgroup_def (X : set G) :
(generated_subgroup X).carrier = ⋂₀ {Y | X ⊆ Y ∧ is_subgroup Y} := rfl

@[simp, to_additive]
lemma generated_subgroup_def' (X : set G) (x : G) :
x ∈ generated_subgroup X ↔ x ∈ ⋂₀ {Y | X ⊆ Y ∧ is_subgroup Y} :=
begin
  rw ← subgroup.mem_carrier,
  rw generated_subgroup_def
end

notation `⟪` X `⟫` := generated_subgroup X

@[simp, to_additive]
lemma subseteq_generated_subgroup (S : set G) : S ⊆ ⟪S⟫ :=
begin
  intros s hs X hX,
  simp at hX,
  obtain ⟨hX₁, hX₂⟩ := hX,
  exact hX₁ hs
end

@[simp, to_additive]
lemma le_generated_subgroup (S : set G) (H : subgroup G) (h : ↑H ⊆ S) : H ≤ generated_subgroup S :=
begin
  rw le_def,
  rw generated_subgroup_def,
  rintros a ha Y ⟨hY₁, hY₂⟩,
  apply hY₁,
  apply h,
  exact ha
end

@[simp, to_additive]
lemma eq_generated_subgroup (H : subgroup G) : generated_subgroup H.carrier = H :=
begin
  ext,
  simp,
  split,
  { intro h,
    exact h H.carrier subset_rfl (is_subgroup_of_subgroup H) },
  { intros hx Y hY sgY,
    exact hY hx }
end

@[to_additive]
def sup (H K : subgroup G) : subgroup G := generated_subgroup (↑H ∪ ↑K)
@[to_additive] instance : has_sup (subgroup G) := ⟨sup⟩

@[to_additive]
lemma sup_def (H K : subgroup G) : H ⊔ K = generated_subgroup (↑H ∪ ↑K) := rfl

@[to_additive]
protected lemma le_sup_left (H K : subgroup G) : H ≤ H ⊔ K :=
begin
  rw sup_def,
  apply le_generated_subgroup,
  exact set.subset_union_left _ _
end

@[to_additive]
protected lemma le_sup_right (H K : subgroup G) : K ≤ H ⊔ K :=
begin
  rw sup_def,
  apply le_generated_subgroup,
  exact set.subset_union_right _ _
end

@[to_additive]
protected lemma sup_le (H K L : subgroup G) (hH : H ≤ L) (hK : K ≤ L) : H ⊔ K ≤ L :=
begin
  rw sup_def,
  rw le_def,
  rw generated_subgroup_def,
  intros Y hY,
  simp at hY,
  exact hY L.carrier ((le_def H L).mp hH) ((le_def K L).mp hK) (is_subgroup_of_subgroup L)
end

@[to_additive]
def Sup (S : set (subgroup G)) : subgroup G := generated_subgroup (⋃₀ (coe '' S))
@[to_additive] instance : has_Sup (subgroup G) := ⟨Sup⟩

@[to_additive]
lemma Sup_def (S : set (subgroup G)) : Sup S = generated_subgroup (⋃₀ (coe '' S)) := rfl

@[to_additive]
protected lemma le_Sup (S : set (subgroup G)) (H : subgroup G) (h : H ∈ S) : H ≤ Sup S :=
begin
  rw Sup_def,
  refine le_generated_subgroup _ _ _,
  intros a ha,
  simp,
  exact ⟨H, h, ha⟩
end

@[to_additive]
protected lemma Sup_le (S : set (subgroup G)) (H : subgroup G)
(h : ∀ (K : subgroup G), K ∈ S → K ≤ H) : Sup S ≤ H :=
begin
  rw Sup_def,
  rw le_def,
  rw generated_subgroup_def,
  intro a,
  simp,
  intro h',
  have := h' H.carrier _ (is_subgroup_of_subgroup H),
  { exact this },
  intros Y hY,
  change Y.carrier ⊆ H.carrier,
  rw ← le_def,
  exact h _ hY
end

@[to_additive]
def univ : subgroup G := {
  carrier := set.univ,
  mul_mem := λ a b ha hb, set.mem_univ _,
  one_mem := set.mem_univ _,
  inv_mem := λ a ha, set.mem_univ _,
}
@[to_additive] instance : has_top (subgroup G) := ⟨univ⟩

@[simp, to_additive]
lemma univ_def : (univ : subgroup G).carrier = set.univ := rfl

@[simp, to_additive]
lemma univ_def' (x : G) : x ∈ (subgroup.univ : subgroup G) :=
begin
  rw ← subgroup.mem_carrier,
  simp
end

@[simp, to_additive]
lemma top_def : (⊤ : subgroup G).carrier = set.univ := rfl

@[to_additive] instance : has_bot (subgroup G) := ⟨trivial⟩

@[simp, to_additive]
lemma bot_def : (⊥ : subgroup G).carrier = {1} := rfl

@[to_additive]
protected lemma le_top (H : subgroup G) : H ≤ ⊤ :=
begin
  rw le_def,
  rw top_def,
  exact set.subset_univ _
end

@[to_additive]
protected lemma bot_le (H : subgroup G) : ⊥ ≤ H :=
begin
  rw le_def,
  rw bot_def,
  simp,
  apply one_mem
end

@[to_additive]
instance : complete_lattice (subgroup G) := {
  sup := sup,
  le := le,
  lt := lt,
  le_refl := subgroup.le_refl,
  le_trans := subgroup.le_trans,
  lt_iff_le_not_le := subgroup.lt_iff_le_not_le,
  le_antisymm := subgroup.le_antisymm,
  le_sup_left := subgroup.le_sup_left,
  le_sup_right := subgroup.le_sup_right,
  sup_le := subgroup.sup_le,
  inf := inf,
  inf_le_left := subgroup.inf_le_left,
  inf_le_right := subgroup.inf_le_right,
  le_inf := subgroup.le_inf,
  Sup := Sup,
  le_Sup := subgroup.le_Sup,
  Sup_le := subgroup.Sup_le,
  Inf := Inf,
  Inf_le := subgroup.Inf_le,
  le_Inf := subgroup.le_Inf,
  top := univ,
  bot := trivial,
  le_top := subgroup.le_top,
  bot_le := subgroup.bot_le,
}

end subgroup

namespace group

variables {G : Type*} [group G] {a b c : G}

-- Various utility lemmas.

@[to_additive]
lemma mul_left_cancel (a : G) (h : a * b = a * c) : b = c :=
begin
  have : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by rw h,
  rwa [← mul_assoc, ← mul_assoc, mul_left_inv, one_mul, one_mul] at this
end

@[simp, to_additive] lemma mul_left_cancel_iff (a : G) : a * b = a * c ↔ b = c :=
⟨mul_left_cancel a, λ h, by rw h⟩

@[simp, to_additive] lemma inv_eq_iff_inv_eq : a⁻¹ = b ↔ b⁻¹ = a :=
begin
  split,
  { intro h,
    rw ← h,
    rw inv_inv },
  { intro h,
    rw ← h,
    rw inv_inv }
end

@[to_additive]
lemma eq_one_of_mul_right_cancel (a : G) (h : a * b = a) : b = 1 :=
begin
  have : a⁻¹ * (a * b) = a⁻¹ * a := by rw h,
  rwa [← mul_assoc, mul_left_inv, one_mul] at this
end

@[to_additive]
lemma eq_one_of_mul_left_cancel (a : G) (h : b * a = a) : b = 1 :=
begin
  have : b * a * a⁻¹ = a * a⁻¹ := by rw h,
  rwa [mul_assoc, mul_right_inv, mul_one] at this
end

@[to_additive]
lemma mul_right_cancel (b : G) (h : a * b = c * b) : a = c :=
begin
  have : a * b  * b⁻¹ = c * b * b⁻¹ := by rw h,
  rwa [mul_assoc, mul_assoc, mul_right_inv, mul_one, mul_one] at this
end

@[simp, to_additive] lemma mul_right_cancel_iff (b : G) : a * b = c * b ↔ a = c :=
⟨mul_right_cancel b, λ h, by rw h⟩

@[to_additive] lemma mul_left_injective (a : G) : function.injective (* a) :=
λ x y h, mul_right_cancel _ h

@[to_additive] lemma mul_right_injective (a : G) : function.injective (λ x, a * x) :=
λ x y h, mul_left_cancel _ h

@[to_additive] lemma mul_ne_mul_left (a : G) : b * a ≠ c * a ↔ b ≠ c :=
begin
  split,
  { intros h₁ h₂,
    rw h₂ at h₁,
    exact h₁ rfl },
  { intros h₁ h₂,
    exact h₁ (mul_right_cancel _ h₂) }
end

@[to_additive] lemma mul_ne_mul_right (a : G) : a * b ≠ a * c ↔ b ≠ c :=
begin
  split,
  { intros h₁ h₂,
    rw h₂ at h₁,
    exact h₁ rfl },
  { intros h₁ h₂,
    exact h₁ (mul_left_cancel _ h₂) }
end

@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
⟨eq_inv_of_mul_eq_one, λ h, by rw [h, mul_left_inv]⟩

@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b :=
by rw [mul_eq_one_iff_eq_inv, inv_inv]

end group

-- Groups have power operations.
-- Unfortunately, in order to get to_additive to work,
-- manually defined additive instances sometimes have weird names.

instance group.nat_pow (G : Type*) [group G] : has_pow G ℕ :=
⟨λ g n, nat.rec (1 : G) (λ k x, x * g) n⟩
instance add_group.nat_pow (G : Type*) [add_group G] : has_scalar ℕ G :=
⟨λ n g, nat.rec (0 : G) (λ k x, x + g) n⟩

@[to_additive]
lemma group.nat_pow_def {G : Type*} [group G] (g : G) (n : ℕ) :
g ^ n = nat.rec (1 : G) (λ k x, x * g) n := rfl

@[simp, to_additive add_group.zero_nsmul]
lemma group.pow_zero {G : Type*} [group G] (g : G) :
g ^ 0 = 1 := rfl

@[simp]
lemma group.pow_one {G : Type*} [group G] (g : G) :
g ^ 1 = g := by { rw group.nat_pow_def, simp }

@[simp]
lemma add_group.one_nsmul {G : Type*} [add_group G] (g : G) :
1 • g = g := by { rw add_group.nat_nsmul_def, simp }

attribute [to_additive add_group.one_nsmul] group.pow_one

@[to_additive]
lemma group.add_nat_pow {G : Type*} [group G] (m n : ℕ) (x : G) :
x ^ (m + n) = x ^ m * x ^ n :=
begin
  rw [group.nat_pow_def, group.nat_pow_def, group.nat_pow_def],
  induction n with k hk,
  { simp,
    rw nat.add_zero },
  { simp,
    rw ← mul_assoc,
    rw ← hk,
    rw nat.add_succ }
end

@[to_additive]
lemma group.sub_nat_pow_of_le {G : Type*} [group G] (m n : ℕ) (x : G) (h : n ≤ m) :
x ^ (m - n) * x ^ n = x ^ m :=
begin
  rw ← group.add_nat_pow,
  rw nat.sub_add_cancel h
end

@[simp, to_additive]
lemma group.one_pow_nat {G : Type*} [group G] (n : ℕ) :
(1 : G) ^ n = 1 :=
begin
  induction n with n hn,
  { simp },
  { change (1 : G) ^ (n + 1) = 1,
    rw group.add_nat_pow,
    simp,
    exact hn }
end

@[to_additive]
lemma group.nat_pow_distrib_of_comm {G : Type*} [group G]
{x y : G} (h : x * y = y * x) (n : ℕ) : (x * y) ^ n = x ^ n * y ^ n :=
begin
  induction n with n hn,
  { simp },
  { rw ← nat.add_one,
    rw group.add_nat_pow,
    rw group.add_nat_pow,
    rw group.add_nat_pow,
    rw hn,
    rw mul_assoc,
    rw mul_assoc,
    congr' 1,
    simp,
    rw ← mul_assoc,
    rw ← mul_assoc,
    congr' 1,
    clear hn, induction n with n hn,
    { simp },
    { rw ← nat.add_one,
      rw group.add_nat_pow,
      simp,
      rw mul_assoc,
      rw ← h,
      rw ← mul_assoc,
      rw hn,
      rw mul_assoc } }
end

instance group.int_pow (G : Type*) [group G] : has_pow G ℤ :=
⟨λ g n, int.rec (λ x, g ^ x) (λ x, g⁻¹ * g⁻¹ ^ x) n⟩
instance add_group.int_pow (G : Type*) [add_group G] : has_scalar ℤ G :=
⟨λ n g, int.rec (λ x, x • g) (λ x, -g + x • -g) n⟩

@[to_additive]
lemma group.int_pow_def {G : Type*} [group G] (g : G) (n : ℤ) :
g ^ n = int.rec (λ x, g ^ x) (λ x, g⁻¹ * g⁻¹ ^ x) n := rfl

@[simp, to_additive]
lemma group.pow_int_of_nat {G : Type*} [group G] (g : G) (n : ℕ) :
g ^ (int.of_nat n) = g ^ n := rfl

@[simp, to_additive]
lemma group.pow_int_coe {G : Type*} [group G] (g : G) (n : ℕ) :
g ^ (n : ℤ) = g ^ n := rfl

@[simp, to_additive add_group.zero_nsmul_int]
lemma group.pow_zero_int {G : Type*} [group G] (g : G) :
g ^ (0 : ℤ) = 1 :=
by { rw ← int.of_nat_zero, rw group.pow_int_of_nat, simp }

@[simp, to_additive add_group.one_nsmul_int]
lemma group.pow_one_int {G : Type*} [group G] (g : G) :
g ^ (1 : ℤ) = g :=
by { rw ← int.of_nat_one, rw group.pow_int_of_nat, simp }

@[simp, to_additive]
lemma group.inv_of_pow_neg_one {G : Type*} [group G] (g : G) :
g ^ (-1 : ℤ) = g⁻¹ :=
by { change g ^ (-[1+ 0]) = g⁻¹, rw group.int_pow_def, simp }

@[to_additive]
lemma group.succ_int_pow {G : Type*} [group G] (n : ℤ) (x : G) :
x ^ (n + 1) = x ^ n * x :=
begin
  induction n,
  { rw [group.int_pow_def, group.int_pow_def],
    rw ← int.of_nat_succ,
    simp,
    change x ^ (n + 1) = x ^ n * x,
    rw group.add_nat_pow,
    simp },
  { induction n,
    { rw group.int_pow_def _ -[1+ 0],
      norm_num },
    { have : -[1+ n_n.succ] + 1 = -[1+ n_n],
      { rw [int.neg_succ_of_nat_eq, int.neg_succ_of_nat_eq],
        norm_num },
      rw this,
      rw [group.int_pow_def, group.int_pow_def],
      dsimp,
      rw mul_assoc,
      rw [group.nat_pow_def, group.nat_pow_def],
      rw mul_assoc,
      rw mul_left_inv,
      rw mul_one } }
end

@[to_additive]
lemma group.succ_int_pow' {G : Type*} [group G] (n : ℤ) (x : G) :
x ^ (n.succ) = x ^ n * x := group.succ_int_pow n x

@[to_additive]
lemma group.pred_int_pow {G : Type*} [group G] (n : ℤ) (x : G) :
x ^ (n - 1) = x ^ n * x⁻¹ :=
begin
  suffices : x ^ (n - 1) = x ^ ((n - 1) + 1) * x⁻¹,
  { simp at this,
    exact this },
  rw group.succ_int_pow,
  rw mul_assoc,
  simp
end

@[to_additive]
lemma group.pred_int_pow' {G : Type*} [group G] (n : ℤ) (x : G) :
x ^ (n.pred) = x ^ n * x⁻¹ := group.pred_int_pow n x

@[to_additive]
lemma group.add_int_pow {G : Type*} [group G] (m n : ℤ) (x : G) :
x ^ (m + n) = x ^ m * x ^ n :=
begin
  induction n,
  { induction n with n hn,
    { simp },
    { rw [
        ← nat.add_one,
        ← int.of_nat_add_of_nat,
        ← int.add_assoc,
        int.of_nat_one,
        group.succ_int_pow, group.succ_int_pow,
        hn, mul_assoc ] } },
  { induction n with n hn,
    { norm_num,
      rw group.pred_int_pow },
    { rw ← nat.add_one,
      rw [
        int.pred_neg_succ_of_nat,
        int.sub_eq_add_neg,
        ← int.add_assoc,
        ← int.sub_eq_add_neg, ← int.sub_eq_add_neg,
        group.pred_int_pow, group.pred_int_pow,
        hn,
        mul_assoc ] } }
end

@[to_additive]
lemma group.int_pow_comm {G : Type*} [group G] (m n : ℤ) (x : G) :
x ^ m * x ^ n = x ^ n * x ^ m :=
begin
  rw ← group.add_int_pow,
  rw ← group.add_int_pow,
  rw int.add_comm
end

@[to_additive]
lemma group.eq_one_of_pow_mul_pow_neg {G : Type*} [group G] (n : ℤ) (x : G) :
x ^ n * x ^ (-n) = 1 :=
begin
  rw ← group.add_int_pow,
  simp
end

@[to_additive]
lemma group.inv_pow_eq_pow_neg {G : Type*} [group G] (n : ℤ) (x : G) :
(x ^ n)⁻¹ = x ^ (-n) :=
begin
  symmetry,
  apply group.eq_of_mul_inv_eq_one,
  rw group.inv_inv,
  rw group.int_pow_comm,
  apply group.eq_one_of_pow_mul_pow_neg
end

@[to_additive]
lemma group.sub_int_pow {G : Type*} [group G] (m n : ℤ) (x : G) :
x ^ (m - n) = x ^ m * (x ^ n)⁻¹ :=
begin
  rw group.inv_pow_eq_pow_neg,
  rw ← group.add_int_pow,
  rw int.sub_eq_add_neg
end

@[to_additive]
lemma group.inv_comm_of_comm {G : Type*} [group G]
{x y : G} (h : x * y = y * x) : x⁻¹ * y = y * x⁻¹ :=
begin
  apply group.eq_of_mul_inv_eq_one,
  rw group.mul_inv_rev,
  rw group.inv_inv,
  rw ← mul_assoc,
  rw mul_assoc x⁻¹ y,
  rw ← h,
  rw mul_assoc,
  rw mul_assoc,
  simp
end

@[to_additive]
lemma group.nat_pow_comm_of_comm {G : Type*} [group G]
{x y : G} (h : x * y = y * x) (n : ℕ) : x ^ n * y = y * x ^ n :=
begin
  induction n with n hn,
  { simp },
  { rw ← nat.add_one,
    rw group.add_nat_pow,
    rw group.pow_one,
    rw mul_assoc,
    rw h,
    rw ← mul_assoc,
    rw hn,
    rw mul_assoc }
end

@[to_additive]
lemma group.pow_comm_of_comm {G : Type*} [group G]
{x y : G} (h : x * y = y * x) (n : ℤ) : x ^ n * y = y * x ^ n :=
begin
  induction n,
  { rw group.pow_int_of_nat,
    apply group.nat_pow_comm_of_comm h },
  { induction n with n hn,
    { rw int.neg_one,
      simp,
      apply group.inv_comm_of_comm h },
    { rw int.pred_neg_succ_of_nat,
      rw group.pred_int_pow,
      rw mul_assoc,
      rw group.inv_comm_of_comm h,
      rw ← mul_assoc,
      rw hn,
      rw mul_assoc } }
end

@[to_additive]
lemma group.nat_pow_comm_pow_of_comm {G : Type*} [group G]
{x y : G} (h : x * y = y * x) (m n : ℕ) : x ^ n * y ^ m = y ^ m * x ^ n :=
begin
  induction m with m hm,
  { simp },
  { rw ← nat.add_one,
    rw group.add_nat_pow,
    rw ← mul_assoc,
    rw group.pow_one,
    rw hm,
    rw mul_assoc,
    rw mul_assoc,
    rw group.nat_pow_comm_of_comm h n }
end

@[to_additive]
lemma group.pow_comm_pow_of_comm {G : Type*} [group G]
{x y : G} (h : x * y = y * x) (m n : ℤ) : x ^ n * y ^ m = y ^ m * x ^ n :=
begin
  induction m,
  { induction n,
    { rw group.pow_int_of_nat,
      rw group.pow_int_of_nat,
      rw group.nat_pow_comm_pow_of_comm h },
    { rw int.neg_succ_of_nat_eq,
      rw ← group.inv_pow_eq_pow_neg,
      have : y ^ int.of_nat m * x ^ (↑n + 1 : ℤ) = x ^ (↑n + 1 : ℤ) * y ^ int.of_nat m,
      { rw int.coe_nat_add_one_out,
        rw group.pow_int_of_nat,
        rw group.pow_int_coe,
        apply group.nat_pow_comm_pow_of_comm h.symm },
      apply group.eq_of_mul_inv_eq_one,
      rw group.mul_inv_rev,
      rw group.inv_inv,
      rw mul_assoc,
      rw ← mul_assoc (y ^ int.of_nat m),
      rw this,
      rw ← mul_assoc,
      rw ← mul_assoc,
      simp } },
  { induction n,
    { rw int.neg_succ_of_nat_eq,
      rw ← group.inv_pow_eq_pow_neg,
      have : y ^ (↑m + 1 : ℤ) * x ^ int.of_nat n = x ^ int.of_nat n * y ^ (↑m + 1 : ℤ),
      { rw int.coe_nat_add_one_out,
        rw group.pow_int_of_nat,
        rw group.pow_int_coe,
        apply group.nat_pow_comm_pow_of_comm h.symm },
      apply group.eq_of_mul_inv_eq_one,
      rw group.mul_inv_rev,
      rw group.inv_inv,
      rw mul_assoc,
      rw ← mul_assoc (y ^ (↑m + 1 : ℤ))⁻¹,
      rw ← group.mul_inv_rev,
      rw ← this,
      rw group.mul_inv_rev,
      rw ← mul_assoc,
      rw ← mul_assoc,
      simp },
    { rw int.neg_succ_of_nat_eq,
      rw int.neg_succ_of_nat_eq,
      rw ← group.inv_pow_eq_pow_neg,
      rw ← group.inv_pow_eq_pow_neg,
      rw ← group.mul_inv_rev,
      rw ← group.mul_inv_rev,
      congr' 1,
      rw int.coe_nat_add_one_out,
      rw int.coe_nat_add_one_out,
      rw group.pow_int_coe,
      rw group.pow_int_coe,
      rw group.nat_pow_comm_pow_of_comm h } }
end

@[to_additive]
lemma group.int_pow_distrib_of_comm {G : Type*} [group G]
{x y : G} (h : x * y = y * x) (n : ℤ) : (x * y) ^ n = x ^ n * y ^ n :=
begin
  induction n,
  { apply group.nat_pow_distrib_of_comm h },
  { rw int.neg_succ_of_nat_eq,
    rw ← group.inv_pow_eq_pow_neg,
    rw ← group.inv_pow_eq_pow_neg,
    rw ← group.inv_pow_eq_pow_neg,
    rw ← group.mul_inv_rev,
    congr' 1,
    rw int.coe_nat_add_one_out,
    rw group.pow_int_coe,
    rw group.pow_int_coe,
    rw group.pow_int_coe,
    rw group.nat_pow_comm_pow_of_comm h.symm,
    apply group.nat_pow_distrib_of_comm h }
end

@[simp, to_additive add_group.nsmul_zero_int]
lemma group.one_pow_int {G : Type*} [group G] (n : ℤ) :
(1 : G) ^ n = 1 :=
begin
  induction n,
  { rw group.pow_int_of_nat,
    simp },
  { rw int.neg_succ_of_nat_eq,
    rw ← group.inv_pow_eq_pow_neg,
    simp,
    rw int.coe_nat_add_one_out,
    rw group.pow_int_coe,
    simp }
end

@[simp, to_additive]
lemma group.pow_neg_one_eq_inv {G : Type*} [group G] (x : G) :
x ^ (-1 : ℤ) = x⁻¹ :=
begin
  apply group.eq_inv_of_mul_eq_one,
  simp
end

@[to_additive]
lemma group.inv_int_pow_eq_int_pow_inv {G : Type*} [group G] (n : ℤ) (x : G) :
x⁻¹ ^ n = (x ^ n)⁻¹ :=
begin
  rw group.inv_pow_eq_pow_neg,
  apply group.eq_of_mul_inv_eq_one,
  rw group.inv_pow_eq_pow_neg,
  rw int.neg_neg,
  rw ← group.int_pow_distrib_of_comm,
  simp, simp
end

@[to_additive]
lemma group.int_pow_neg_eq_inv_pow {G : Type*} [group G] (n : ℤ) (x : G) :
x ^ (-n) = x⁻¹ ^ n :=
begin
  rw group.inv_int_pow_eq_int_pow_inv,
  rw group.inv_pow_eq_pow_neg
end

@[to_additive]
lemma group.nat_pow_pow {G : Type*} [group G] (m n : ℕ) (x : G) :
(x ^ m) ^ n = x ^ (m * n) :=
begin
  induction n with n hn,
  { simp },
  { rw ← nat.add_one,
    rw nat.left_distrib,
    rw nat.mul_one,
    rw group.add_nat_pow,
    rw group.add_nat_pow,
    rw hn,
    simp }
end

@[to_additive]
lemma group.pow_pow {G : Type*} [group G] (m n : ℤ) (x : G) :
(x ^ m) ^ n = x ^ (m * n) :=
begin
  induction n,
  { induction n with n hn,
    { simp },
    { rw int.of_nat_succ,
      rw group.succ_int_pow,
      rw int.distrib_left,
      rw int.mul_one,
      rw group.add_int_pow,
      rw hn } },
  { induction n with n hn,
    { change (x ^ m) ^ (-1 : ℤ) = x ^ (m * (-1)),
      simp,
      apply group.inv_pow_eq_pow_neg },
    { rw int.pred_neg_succ_of_nat,
      rw int.sub_eq_add_neg,
      rw int.distrib_left,
      rw group.add_int_pow,
      rw group.add_int_pow,
      simp,
      rw hn,
      rw group.inv_pow_eq_pow_neg } }
end

@[to_additive]
lemma subgroup.nat_pow_mem {G : Type*} [group G] (H : subgroup G) {x : G} {n : ℕ} (h : x ∈ H) : x ^ n ∈ H :=
begin
  induction n with n hn,
  { simp, exact subgroup.one_mem H },
  { rw nat.succ_eq_add_one,
    rw group.add_nat_pow,
    simp,
    exact subgroup.mul_mem H hn h }
end

@[to_additive]
lemma subgroup.int_pow_mem {G : Type*} [group G] (H : subgroup G) {x : G} {n : ℤ}
(h : x ∈ H) : x ^ n ∈ H :=
begin
  induction n,
  { simp, apply subgroup.nat_pow_mem, exact h },
  { induction n with n hn,
    { rw int.neg_one, rw group.pow_neg_one_eq_inv, exact subgroup.inv_mem H h },
    { rw int.neg_succ_of_nat_eq at *,
      simp at *,
      rw group.add_int_pow,
      apply subgroup.mul_mem,
      { simp, exact subgroup.inv_mem H h },
      { exact hn } } }
end

noncomputable def decidable_pow {G : Type*} [group G] (x : G) :
decidable_pred (λ (n : ℕ), 0 < n ∧ x ^ n = 1) :=
classical.dec_pred _
noncomputable def decidable_smul {G : Type*} [add_group G] (x : G) :
decidable_pred (λ (n : ℕ), 0 < n ∧ n • x = 0) :=
classical.dec_pred _

attribute [to_additive decidable_smul] decidable_pow
local attribute [instance] decidable_pow
local attribute [instance] decidable_smul

-- We have to define these two separately because pow and smul take
-- arguments in a different order.
noncomputable def group.order {G : Type*} [group G] (x : G) : enat :=
enat.find (λ n, 0 < n ∧ x ^ n = 1)
noncomputable def add_group.order {G : Type*} [add_group G] (x : G) : enat :=
enat.find (λ n, 0 < n ∧ n • x = 0)

attribute [to_additive] group.order

lemma group.order_def {G : Type*} [group G] (x : G) :
group.order x = enat.find (λ n, 0 < n ∧ x ^ n = 1) := rfl
lemma add_group.order_def {G : Type*} [add_group G] (x : G) :
add_group.order x = enat.find (λ n, 0 < n ∧ n • x = 0) := rfl

attribute [to_additive] group.order_def

lemma enat.sat_of_find_eq_some {P : ℕ → Prop} [decidable_pred P] {n : ℕ} (h : enat.find P = enat.some n) : P n :=
begin
  have dom_some := enat.dom_some n,
  rw ← h at dom_some,
  convert nat.find_spec dom_some,
  rw ← enat.find_get P dom_some,
  symmetry,
  rw enat.get_eq_iff_eq_some,
  exact h
end

@[to_additive]
lemma group.zero_lt_order {G : Type*} [group G] {x : G} {n : ℕ} (h : group.order x = enat.some n) : 0 < n :=
begin
  rw group.order_def at h,
  exact (enat.sat_of_find_eq_some h).1
end

@[to_additive]
lemma group.zero_lt_order_int {G : Type*} [group G] {x : G} {n : ℕ} (h : group.order x = enat.some n) : 0 < (n : ℤ) :=
begin
  simp,
  exact group.zero_lt_order h
end

@[to_additive]
lemma group.zero_ne_order_int {G : Type*} [group G] {x : G} {n : ℕ} (h : group.order x = enat.some n) : 0 ≠ (n : ℤ) :=
begin
  apply ne_of_lt,
  exact group.zero_lt_order_int h
end

@[to_additive]
lemma group.eq_one_of_pow_order {G : Type*} [group G] {x : G} {n : ℕ} (h : group.order x = enat.some n) : x ^ n = 1 :=
begin
  rw group.order_def at h,
  exact (enat.sat_of_find_eq_some h).2
end

@[to_additive]
lemma group.eq_one_of_int_pow_order {G : Type*} [group G] {x : G} {n : ℕ} (h : group.order x = enat.some n) : x ^ (n : ℤ) = 1 :=
begin
  rw group.order_def at h,
  exact (enat.sat_of_find_eq_some h).2
end

@[to_additive]
lemma group.eq_one_of_pow_order_dvd {G : Type*} [group G] {x : G} {n m : ℕ} (h : group.order x = enat.some n) (hm : n ∣ m) : x ^ m = 1 :=
begin
  obtain ⟨c, hc⟩ := hm,
  rw hc,
  rw ← group.nat_pow_pow,
  rw group.eq_one_of_pow_order h,
  simp
end

@[to_additive]
lemma group.order_dvd_of_nat_pow_eq_one {G : Type*} [group G] {x : G} {n m : ℕ} (hord : group.order x = enat.some n) (h : x ^ m = 1) : n ∣ m :=
begin
  have small_eq_zero : ∀ k < n, x ^ k = 1 → k = 0,
  { intros k hk h,
    by_contradiction ne_zero,
    unfold group.order at hord,
    have := enat.find_le (λ n, 0 < n ∧ x ^ n = 1) k ⟨pos_iff_ne_zero.mpr ne_zero, h⟩,
    rw [hord, enat.some_eq_coe, enat.coe_le_coe] at this,
    exact nat.lt_le_antisymm hk this },
  apply nat.dvd_of_mod_eq_zero,
  have := nat.div_add_mod m n,
  rw ← this at h,
  rw group.add_nat_pow at h,
  rw ← group.nat_pow_pow at h,
  rw group.eq_one_of_pow_order hord at h,
  simp at h,
  exact small_eq_zero _ (nat.mod_lt m (group.zero_lt_order hord)) h
end

@[to_additive]
lemma group.eq_one_iff_nat_pow_order_dvd {G : Type*} [group G] {x : G} {n m : ℕ} (h : group.order x = enat.some n) : n ∣ m ↔ x ^ m = 1 :=
⟨group.eq_one_of_pow_order_dvd h, group.order_dvd_of_nat_pow_eq_one h⟩

@[to_additive]
theorem group.eq_one_iff_int_pow_order_dvd {G : Type*} [group G] {x : G} {n : ℕ} {m : ℤ} (h : group.order x = enat.some n) : ↑n ∣ m ↔ x ^ m = 1 :=
begin
  induction m,
  { rw int.of_nat_eq_coe,
    rw int.coe_nat_dvd,
    dsimp,
    rw group.eq_one_iff_nat_pow_order_dvd h },
  { rw int.neg_succ_of_nat_eq,
    rw ← int.dvd_nat_abs,
    rw int.coe_nat_dvd,
    rw int.nat_abs_neg,
    rw ← int.coe_nat_succ,
    rw int.nat_abs_of_nat,
    rw ← group.inv_pow_eq_pow_neg,
    rw group.inv_eq_iff_inv_eq,
    rw group.one_inv,
    rw group.pow_int_coe,
    rw group.eq_one_iff_nat_pow_order_dvd h,
    exact comm }
end

@[to_additive]
lemma group.order_finite_of_finite {G : Type*} [group G] [fintype G] (x : G) :
(group.order x).dom :=
begin
  apply enat.find_dom,
  by_contradiction h,
  push_neg at h,
  obtain ⟨r, s, r_ne_s, hrs⟩ := fintype.exists_ne_map_eq_of_infinite (λ (n : ℕ), x ^ n),
  dsimp at hrs,
  wlog : r < s,
  { exact ne.lt_or_lt r_ne_s },
  have : x ^ (s - r) = 1,
  { apply group.mul_right_cancel (x ^ r),
    rw group.sub_nat_pow_of_le,
    { rw hrs, simp },
    { exact le_of_lt case } },
  refine h (s - r) _ this,
  exact tsub_pos_of_lt case
end

@[to_additive]
noncomputable def group.order_of_finite {G : Type*} [group G] [fintype G] (x : G) : ℕ :=
(group.order x).get (group.order_finite_of_finite x)

@[to_additive]
lemma group.order_eq_some_order_of_finite {G : Type*} [group G] [fintype G] (x : G) :
group.order x = enat.some (group.order_of_finite x) :=
begin
  unfold group.order_of_finite,
  rw ← enat.get_eq_iff_eq_some
end

@[to_additive]
lemma group.zero_lt_order_finite {G : Type*} [group G] [fintype G] (x : G) : 0 < group.order_of_finite x :=
group.zero_lt_order (group.order_eq_some_order_of_finite x)

end notes
