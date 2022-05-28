import data.list.cycle
import data.nat.modeq
import ia.groups.hom

namespace notes

@[reducible] def sym (X : Type*) := X ≃ X

instance {X : Type*} : semigroup (sym X) := ⟨λ σ τ υ, rfl⟩
instance {X : Type*} : monoid (sym X) := ⟨λ σ, by simp, λ σ, by simp⟩
instance {X : Type*} : group (sym X) := ⟨λ σ, by simp, λ σ, by simp⟩

@[reducible] def sym_fin := sym ∘ fin

-- Cycles

structure cycle_perm (X : Type*) :=
(cy : cycle X)
(nodup : cy.nodup)

variables {X : Type*} [decidable_eq X]

def cycle_perm.next_if_mem (c : cycle_perm X) (x : X) :=
dite (x ∈ c.cy) (c.cy.next c.nodup x) (λ _, x)

lemma cycle_perm.next_if_mem_of_mem {c : cycle_perm X} {x : X} (h : x ∈ c.cy) :
cycle_perm.next_if_mem c x = c.cy.next c.nodup x h :=
begin
  unfold cycle_perm.next_if_mem,
  rw dite_eq_iff, simp, left, exact h
end

lemma cycle_perm.next_if_mem_of_not_mem {c : cycle_perm X} {x : X} (h : x ∉ c.cy) :
cycle_perm.next_if_mem c x = x :=
begin
  unfold cycle_perm.next_if_mem,
  rw dite_eq_iff, simp, right, exact h
end

def cycle_perm.prev_if_mem (c : cycle_perm X) (x : X) :=
dite (x ∈ c.cy) (c.cy.prev c.nodup x) (λ _, x)

lemma cycle_perm.prev_if_mem_of_mem {c : cycle_perm X} {x : X} (h : x ∈ c.cy) :
cycle_perm.prev_if_mem c x = c.cy.prev c.nodup x h :=
begin
  unfold cycle_perm.prev_if_mem,
  rw dite_eq_iff, simp, left, exact h
end

lemma cycle_perm.prev_if_mem_of_not_mem {c : cycle_perm X} {x : X} (h : x ∉ c.cy) :
cycle_perm.prev_if_mem c x = x :=
begin
  unfold cycle_perm.prev_if_mem,
  rw dite_eq_iff, simp, right, exact h
end

instance : has_coe (cycle_perm X) (sym X) := ⟨λ c, ⟨
  cycle_perm.next_if_mem c,
  cycle_perm.prev_if_mem c,
  begin
    intro x,
    by_cases x ∈ c.cy,
    { rw cycle_perm.next_if_mem_of_mem h,
      rw cycle_perm.prev_if_mem_of_mem (cycle.next_mem c.cy c.nodup x h),
      simp },
    { rw cycle_perm.next_if_mem_of_not_mem h,
      rw cycle_perm.prev_if_mem_of_not_mem h }
  end,
  begin
    intro x,
    by_cases x ∈ c.cy,
    { rw cycle_perm.prev_if_mem_of_mem h,
      rw cycle_perm.next_if_mem_of_mem (cycle.prev_mem c.cy c.nodup x h),
      simp },
    { rw cycle_perm.prev_if_mem_of_not_mem h,
      rw cycle_perm.next_if_mem_of_not_mem h }
  end
⟩⟩

lemma cycle_perm.act_def (c : cycle_perm X) (x : X) :
c x = cycle_perm.next_if_mem c x := rfl

@[simp]
lemma cycle_perm.act_of_not_mem {c : cycle_perm X} {x : X} (h : x ∉ c.cy) : c x = x :=
by rw [cycle_perm.act_def, cycle_perm.next_if_mem_of_not_mem h]

@[simp]
lemma cycle_perm.act_mem_of_mem {c : cycle_perm X} {x : X} (h : x ∈ c.cy) : c x ∈ c.cy :=
begin
  rw cycle_perm.act_def,
  rw cycle_perm.next_if_mem_of_mem h,
  simp
end

@[simp]
lemma cycle_perm.act_mem_iff_mem (c : cycle_perm X) (x : X) : x ∈ c.cy ↔ c x ∈ c.cy :=
begin
  split,
  { intro h, exact cycle_perm.act_mem_of_mem h },
  { intro h, by_contradiction g,
    rw cycle_perm.act_of_not_mem g at h,
    exact g h }
end

@[simp]
lemma cycle_perm.act_not_mem_of_not_mem {c : cycle_perm X} {x : X} (h : x ∉ c.cy) : c x ∉ c.cy :=
by { rw cycle_perm.act_of_not_mem h, exact h }

@[simp]
lemma cycle_perm.act_not_mem_iff_not_mem (c : cycle_perm X) (x : X) : x ∉ c.cy ↔ c x ∉ c.cy :=
by rw cycle_perm.act_mem_iff_mem

def cycle_perm.disjoint (c d : cycle_perm X) : Prop := ∀ (x : X), x ∈ c.cy → x ∉ d.cy

lemma cycle_perm.disjoint.symm {c d : cycle_perm X} :
c.disjoint d → d.disjoint c := λ h x hx hc, h x hc hx

lemma cycle_perm.disjoint.symm_iff (c d : cycle_perm X) :
c.disjoint d ↔ d.disjoint c := ⟨cycle_perm.disjoint.symm, cycle_perm.disjoint.symm⟩

lemma cycle_perm.comm_of_disjoint (c d : cycle_perm X) (hcd : cycle_perm.disjoint c d) :
(c : sym X) * d = d * c :=
begin
  ext x,
  change c (d x) = d (c x),
  by_cases x ∈ c.cy,
  { rw cycle_perm.act_of_not_mem (hcd x h),
    rw cycle_perm.act_of_not_mem (hcd _ (cycle_perm.act_mem_of_mem h)) },
  { rw cycle_perm.act_of_not_mem h,
    by_cases x ∈ d.cy,
    { rw cycle_perm.act_of_not_mem (hcd.symm _ (cycle_perm.act_mem_of_mem h) : d x ∉ c.cy) },
    { rw cycle_perm.act_of_not_mem,
      rw cycle_perm.act_of_not_mem,
      assumption, assumption } }
end

-- Cycle decomposition

variable {n : ℕ}

lemma sym_fin.ex_order (σ : sym_fin n) (x : fin n) :
∃ (n_1 : ℕ), (λ (n_1 : ℕ), 0 < n_1 ∧ (σ ^ n_1) x = x) n_1 :=
begin
  obtain ⟨a, b, hne, hab⟩ := fintype.exists_ne_map_eq_of_infinite (λ (n : ℕ), (σ ^ n) x),
  wlog : a < b,
  { exact ne.lt_or_lt hne },
  dsimp at hab,
  refine ⟨b - a, _, _⟩,
  { exact lt_tsub_comm.mp case },
  have : σ ^ b = (σ ^ a) * (σ ^ (b - a)),
  { rw group.nat_pow_comm_pow_of_comm,
    rw group.sub_nat_pow_of_le,
    exact le_of_lt case,
    refl },
  rw this at hab,
  symmetry,
  exact equiv.injective _ hab
end

def sym_fin.order (σ : sym_fin n) (x : fin n) : ℕ :=
@nat.find (λ n, 0 < n ∧ (σ ^ n) x = x) _ (sym_fin.ex_order σ x)

@[simp]
lemma sym_fin.order_pos (σ : sym_fin n) (x : fin n) : 0 < σ.order x :=
by { unfold sym_fin.order, simp }

@[simp]
lemma sym_fin.pow_order (σ : sym_fin n) (x : fin n) : (σ ^ σ.order x) x = x :=
(nat.find_spec (sym_fin.ex_order σ x)).right

@[simp]
lemma sym_fin.pow_pow_order (σ : sym_fin n) (x : fin n) (n : ℕ) :
((σ ^ σ.order x) ^ n) x = x :=
begin
  induction n,
  { simp },
  { rw nat.succ_eq_add_one,
    rw nat.add_comm,
    rw group.add_nat_pow,
    simp,
    rw n_ih,
    exact sym_fin.pow_order σ x }
end

def sym_fin.orbit_of (σ : sym_fin n) (x : fin n) : list (fin n) :=
list.map (λ n, (σ ^ n) x) $ list.range (sym_fin.order σ x)

@[simp]
lemma sym_fin.orbit_length_eq_order (σ : sym_fin n) (x : fin n) :
(σ.orbit_of x).length = σ.order x :=
by { unfold sym_fin.orbit_of, simp }

@[simp]
lemma sym_fin.orbit_of_nth (σ : sym_fin n) (x : fin n) (k : ℕ) :
(σ.orbit_of x).nth k = if k < σ.order x then some ((σ ^ k) x) else none :=
begin
  split_ifs,
  { unfold sym_fin.orbit_of,
    simp,
    exact ⟨k, list.nth_range h, rfl⟩ },
  { rw list.nth_eq_none_iff,
    simp,
    exact not_lt.mp h }
end

lemma sym_fin.eq_pow_of_mem_orbit_of {σ : sym_fin n} {x y : fin n}
(h : y ∈ σ.orbit_of x) : ∃ (n : ℕ), n < σ.order x ∧ (σ ^ n) x = y :=
begin
  unfold sym_fin.orbit_of at h,
  simp at h,
  exact h
end

@[simp]
lemma sym_fin.mem_orbit_of_ext (σ : sym_fin n) (x y : fin n) :
y ∈ σ.orbit_of x ↔ ∃ (n : ℕ), (σ ^ n) x = y :=
begin
  unfold sym_fin.orbit_of,
  simp,
  split,
  { rintro ⟨a, ha₁, ha₂⟩,
    exact ⟨a, ha₂⟩ },
  { rintro ⟨a, ha⟩,
    refine ⟨a % σ.order x, _, _⟩,
    { apply nat.mod_lt,
      simp },
    { rw ← nat.div_add_mod a (σ.order x) at ha,
      rw ← ha,
      rw nat.add_comm,
      rw group.add_nat_pow,
      simp,
      rw ← group.nat_pow_pow,
      simp } }
end

@[simp]
lemma sym_fin.mem_orbit_of_self (σ : sym_fin n) (x : fin n) : x ∈ σ.orbit_of x :=
by { simp, exact ⟨0, rfl⟩ }

@[simp]
lemma sym_fin.orbit_of_nodup (σ : sym_fin n) (x : fin n) : (sym_fin.orbit_of σ x).nodup :=
begin
  unfold sym_fin.orbit_of,
  rw list.nodup_map_iff_inj_on,
  { intros a ha b hb hab,
    by_contradiction hne,
    wlog : a < b,
    { exact ne.lt_or_lt hne },
    have : (σ ^ (b - a)) x = x,
    { have : σ ^ b = (σ ^ a) * (σ ^ (b - a)),
      { rw group.nat_pow_comm_pow_of_comm,
        rw group.sub_nat_pow_of_le,
        exact le_of_lt case,
        refl },
      rw this at hab,
      symmetry,
      exact equiv.injective _ hab },
    have : b - a < σ.order x,
    { rw list.mem_range at ha hb,
      apply lt_of_le_of_lt _ hb,
      norm_num },
    unfold sym_fin.order at this,
    rw nat.lt_find_iff at this,
    refine this (b - a) (le_refl _) ⟨_, _⟩,
    { norm_num, exact case },
    { assumption } },
  { exact list.nodup_range _ }
end

def sym_fin.cycle_of (σ : sym_fin n) (x : fin n) : cycle (fin n) :=
↑(sym_fin.orbit_of σ x)

@[simp]
lemma sym_fin.mem_cycle_of (σ : sym_fin n) (x y : fin n) :
y ∈ σ.cycle_of x ↔ y ∈ σ.orbit_of x := iff.rfl

@[simp]
lemma sym_fin.mem_cycle_of_self (σ : sym_fin n) (x : fin n) : x ∈ σ.cycle_of x :=
by simp

@[simp]
lemma sym_fin.cycle_of_nodup (σ : sym_fin n) (x : fin n) : (sym_fin.cycle_of σ x).nodup :=
by { unfold sym_fin.cycle_of, simp }

def sym_fin.cycle_perm_of (σ : sym_fin n) (x : fin n) : cycle_perm (fin n) :=
⟨sym_fin.cycle_of σ x, sym_fin.cycle_of_nodup σ x⟩

@[simp]
lemma sym_fin.mem_cycle_perm_of (σ : sym_fin n) (x y : fin n) :
y ∈ (σ.cycle_perm_of x).cy ↔ y ∈ σ.cycle_of x := iff.rfl

@[simp]
lemma sym_fin.cycle_perm_next_eq_cycle_next (σ : sym_fin n) (x y : fin n)
(hmem : y ∈ σ.cycle_of x) :
(σ.cycle_perm_of x).cy.next (sym_fin.cycle_of_nodup σ x) y ((sym_fin.mem_cycle_perm_of σ x y).mp hmem) =
(σ.cycle_of x).next (sym_fin.cycle_of_nodup σ x) y hmem :=
by unfold sym_fin.cycle_perm_of

@[simp]
lemma sym_fin.mem_cycle_perm_of_self (σ : sym_fin n) (x : fin n) : x ∈ (σ.cycle_perm_of x).cy :=
by simp

lemma quotient.hrec_on'_eq_hrec_on {α : Sort u_1} [s₁ : setoid α] {φ : quotient s₁ → Sort*}
(qa : quotient s₁) (f : Π (a : α), φ (quotient.mk' a)) (c : ∀ (a₁ a₂ : α), a₁ ≈ a₂ → f a₁ == f a₂)
: quotient.hrec_on' qa f c = quotient.hrec_on qa f c := rfl

lemma cycle_next_eq_list_next {α : Type*} [decidable_eq α] (s : list α) (hs : s.nodup) (x : α) (hx : x ∈ s) :
s.next x hx = (↑s : cycle α).next hs x hx := by refl

lemma range_eq_cons_cons (a : ℕ) : ∃ ys, list.range (a + 2) = 0 :: 1 :: ys :=
begin
  induction a,
  { have : list.range 2 = [0, 1] := rfl,
    rw this,
    exact ⟨[], rfl⟩ },
  { obtain ⟨ys, hys⟩:= a_ih,
    refine ⟨ys ++ [a_n + 2], _⟩,
    rw list.range_succ,
    rw hys,
    rw list.cons_append,
    rw list.cons_append }
end

@[simp]
lemma sym_fin.cycle_perm_act (σ : sym_fin n) (x : fin n) : sym_fin.cycle_perm_of σ x x = σ x :=
begin
  rw cycle_perm.act_def,
  rw cycle_perm.next_if_mem_of_mem (sym_fin.mem_cycle_perm_of_self σ x),
  have := sym_fin.cycle_perm_next_eq_cycle_next σ x x (sym_fin.mem_cycle_of_self σ x),
  convert this,
  unfold sym_fin.cycle_of,
  unfold sym_fin.orbit_of,
  convert cycle_next_eq_list_next (list.map (λ (n_1 : ℕ), (σ ^ n_1) x) (list.range (σ.order x))) _ _ _,
  by_cases σ.order x ≤ 1,
  { have ord_one := ge_antisymm (nat.succ_le_of_lt $ sym_fin.order_pos σ x) h,
    suffices : list.map (λ (m : ℕ), (σ ^ m) x) (list.range (σ.order x)) = [x],
    { simp_rw this,
      rw list.next_singleton x x,
      obtain ⟨_, hord⟩ := nat.find_spec (sym_fin.ex_order σ x),
      unfold sym_fin.order at ord_one,
      rw ord_one at hord,
      simp at hord,
      exact hord },
    rw ord_one,
    have : list.range 1 = [0] := rfl,
    rw this,
    simp },
  { obtain ⟨k, hk⟩ : ∃ (k : ℕ), σ.order x = k.succ.succ,
    { obtain ⟨k₁, hk₁⟩ := nat.exists_eq_succ_of_ne_zero (_ : σ.order x ≠ 0),
      obtain ⟨k₂, hk₂⟩ := nat.exists_eq_succ_of_ne_zero (_ : k₁ ≠ 0),
      refine ⟨k₂, _⟩,
      rw hk₁, rw hk₂,
      { intro hzero,
        rw hzero at hk₁,
        rw hk₁ at h,
        exact h (le_refl 1) },
      { intro hzero,
        rw hzero at h,
        exact h (zero_le 1) } },
    obtain ⟨ys, hys⟩ := range_eq_cons_cons k,
    rw ← nat.succ_eq_add_one at hys,
    rw ← nat.succ_eq_add_one at hys,
    rw ← hk at hys,
    simp_rw hys,
    simp,
    rw list.next_cons_cons_eq _ x (σ x) }
end

@[simp]
lemma sym_fin.cycle_perm_eq_of_mem_orbit (σ : sym_fin n) (x y : fin n)
(horb : y ∈ σ.orbit_of x) : σ.cycle_perm_of x = σ.cycle_perm_of y :=
begin
  unfold sym_fin.cycle_perm_of,
  unfold sym_fin.cycle_of,
  simp,
  rw list.is_rotated_iff_mod,
  obtain ⟨k, hk₁, hk₂⟩ := sym_fin.eq_pow_of_mem_orbit_of horb,
  refine ⟨k, _, _⟩,
  { unfold sym_fin.orbit_of,
    simp,
    exact le_of_lt hk₁ },
  { ext a a',
    simp,
    by_cases case : a < (σ.orbit_of x).length,
    { rw list.nth_rotate case,
      simp at case ⊢,
      have : (a + k) % σ.order x < σ.order x,
      { apply nat.mod_lt,
        simp },
      have : a < σ.order y,
      { sorry },
      split_ifs,
      suffices : (σ ^ ((a + k) % σ.order x)) x = (σ ^ a) y,
      { rw this },
      have rw_ak : (↑a + ↑k : ℤ) % (σ.order x) = (↑a + ↑k) - ↑(σ.order x) * ((↑a + ↑k) / (σ.order x))
      := int.mod_def (↑a + ↑k) ↑(sym_fin.order σ x),
      rw ← group.pow_int_coe,
      rw int.coe_nat_mod,
      rw int.coe_nat_add,
      rw rw_ak,
      rw int.sub_eq_add_neg,
      rw int.add_comm,
      rw group.add_int_pow,
      rw ← int.coe_nat_add,
      rw group.pow_int_coe,
      rw group.add_nat_pow,
      simp,
      rw hk₂, }
     }
end

end notes
