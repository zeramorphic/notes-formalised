import ia.groups.axioms

namespace notes

open group

-- Structures for homomorphisms and specific types

@[ext]
structure hom (G H : Type*) [group G] [group H] :=
(to_fun : G → H)
(map_mul : ∀ x y, to_fun (x * y) = to_fun x * to_fun y)

@[ext]
structure add_hom (G H : Type*) [add_group G] [add_group H] :=
(to_fun : G → H)
(map_add : ∀ x y, to_fun (x + y) = to_fun x + to_fun y)

attribute [to_additive add_hom] hom

infixr ` →* `:25 := hom
infixr ` →+ `:25 := add_hom

-- `hom_class F A B` states that `F` is a type of multiplication-preserving morphisms.
class hom_class (F : Type*) (A B : out_param $ Type*) [group A] [group B]
  extends fun_like F A (λ _, B) :=
(map_op : ∀ (f : F) (x y : A), f (x * y) = (f x) * (f y))

-- `add_hom_class F A B` states that `F` is a type of addition-preserving morphisms.
class add_hom_class (F : Type*) (A B : out_param $ Type*) [add_group A] [add_group B]
  extends fun_like F A (λ _, B) :=
(map_op : ∀ (f : F) (x y : A), f (x + y) = (f x) + (f y))

attribute [to_additive add_hom_class] hom_class

@[ext, ancestor hom]
structure hom.mono (G H : Type*) [group G] [group H] extends hom G H :=
(inj : function.injective to_fun)

@[ext, ancestor add_hom]
structure add_hom.mono (G H : Type*) [add_group G] [add_group H] extends add_hom G H :=
(inj : function.injective to_fun)

@[ext, ancestor hom]
structure hom.epi (G H : Type*) [group G] [group H] extends hom G H :=
(surj : function.surjective to_fun)

@[ext, ancestor add_hom]
structure add_hom.epi (G H : Type*) [add_group G] [add_group H] extends add_hom G H :=
(surj : function.surjective to_fun)

@[ext, ancestor hom]
structure hom.iso (G H : Type*) [group G] [group H] extends hom G H :=
(bij : function.bijective to_fun)

@[ext, ancestor add_hom]
structure add_hom.iso (G H : Type*) [add_group G] [add_group H] extends add_hom G H :=
(bij : function.bijective to_fun)

attribute [to_additive] hom.mono
attribute [to_additive] hom.epi
attribute [to_additive] hom.iso

class hom.mono_class (F : Type*) (A B : out_param $ Type*) [group A] [group B]
  extends hom_class F A B :=
(inj : ∀ (f : F), function.injective f)

class add_hom.mono_class (F : Type*) (A B : out_param $ Type*) [add_group A] [add_group B]
  extends add_hom_class F A B :=
(inj : ∀ (f : F), function.injective f)

class hom.epi_class (F : Type*) (A B : out_param $ Type*) [group A] [group B]
  extends hom_class F A B :=
(surj : ∀ (f : F), function.surjective f)

class add_hom.epi_class (F : Type*) (A B : out_param $ Type*) [add_group A] [add_group B]
  extends add_hom_class F A B :=
(surj : ∀ (f : F), function.surjective f)

class hom.iso_class (F : Type*) (A B : out_param $ Type*) [group A] [group B]
  extends hom_class F A B :=
(bij : ∀ (f : F), function.bijective f)

class add_hom.iso_class (F : Type*) (A B : out_param $ Type*) [add_group A] [add_group B]
  extends add_hom_class F A B :=
(bij : ∀ (f : F), function.bijective f)

attribute [to_additive] hom.mono_class
attribute [to_additive] hom.epi_class
attribute [to_additive] hom.iso_class

infixr ` ↪* `:25 := hom.mono
infixr ` ↠* `:25 := hom.epi
infix ` ≅ `:25 := hom.iso
infixr ` ↪+ `:25 := add_hom.add_mono
infixr ` ↠+ `:25 := hom.add_epi
infix ` ≅+ `:25 := hom.add_iso

namespace hom

variables {G H K L : Type*} [group G] [group H] [group K] [group L] -- groups
variables {Φ Ψ Χ : Type*} -- homomorphisms (note: Χ is a capital χ not a Latin capital x)

@[simp, to_additive] lemma map_op [hom_class Φ G H]
  (φ : Φ) (x y : G) : φ (x * y) = (φ x) * (φ y) :=
hom_class.map_op φ x y

@[simp, to_additive] lemma hom_coe_def [hom_class Φ G H]
  (φ : Φ) (x : G) : fun_like.coe φ x = φ x := rfl

@[to_additive]
instance to_hom_class {G H : Type*} [group G] [group H] : hom_class (G →* H) G H :=
{ coe := hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_op := hom.map_mul }

@[to_additive]
instance to_mono_class : mono_class (G ↪* H) G H := {
  coe := λ φ, φ.to_fun,
  coe_injective' := begin
    intros f g h,
    dsimp at h,
    ext,
    rw h
  end,
  map_op := λ φ, φ.map_mul,
  inj := begin
    intros φ x y,
    apply φ.inj
  end,
}

@[to_additive]
instance to_epi_class : epi_class (G ↠* H) G H := {
  coe := λ φ, φ.to_fun,
  coe_injective' := begin
    intros f g h,
    dsimp at h,
    ext,
    rw h
  end,
  map_op := λ φ, φ.map_mul,
  surj := begin
    intros φ x,
    apply φ.surj
  end,
}

@[to_additive]
instance to_iso_class : iso_class (G ≅ H) G H := {
  coe := λ φ, φ.to_fun,
  coe_injective' := begin
    intros f g h,
    dsimp at h,
    ext,
    rw h
  end,
  map_op := λ φ, φ.map_mul,
  bij := begin
    intro φ,
    split,
    { intros x y,
      apply φ.bij.1 },
    { intro x,
      apply φ.bij.2 }
  end,
}

@[simp, to_additive]
lemma mono_inj [mono_class Φ G H] (φ : Φ) : function.injective φ :=
mono_class.inj φ

@[simp, to_additive]
lemma epi_surj [epi_class Φ G H] (φ : Φ) : function.surjective φ :=
epi_class.surj φ

@[simp, to_additive]
lemma iso_bij [iso_class Φ G H] (φ : Φ) : function.bijective φ :=
iso_class.bij φ

@[to_additive, priority 100]
instance mono_of_iso [iso_class Φ G H] : mono_class Φ G H := {
  inj := λ f, (iso_bij f).1
}

@[to_additive, priority 100]
instance epi_of_iso [iso_class Φ G H] : epi_class Φ G H := {
  surj := λ f, (iso_bij f).2
}

-- TODO: why is this noncomputable?

@[to_additive]
lemma iso_of_mono_surj [mono_class Φ G H] {φ : Φ} (h : function.surjective φ) :
Σ' (ψ : G ≅ H), fun_like.coe ψ = fun_like.coe φ := ⟨
  ⟨⟨fun_like.coe φ, λ x y, by simp⟩,
  ⟨by simp, h⟩⟩,
  rfl
⟩

-- Basic lemmas about homomorphisms

@[to_additive]
lemma map_one [hom_class Φ G H] (φ : Φ) : φ 1 = 1 :=
begin
  have : φ (1 * 1) = φ 1 * φ 1 := by rw map_op,
  rw one_mul at this,
  let k := φ 1,
  exact group.eq_one_of_mul_right_cancel this.symm
end

@[to_additive]
lemma map_inv [hom_class Φ G H] (φ : Φ) (x : G) : φ x⁻¹ = (φ x)⁻¹ :=
begin
  apply group.eq_inv_of_mul_eq_one,
  rw ← map_op,
  rw mul_left_inv,
  rw map_one
end

-- Homomorphism composition

@[to_additive]
def comp [hom_class Φ G H] [hom_class Ψ H K] (ψ : Ψ) (φ : Φ) : G →* K :=
⟨ψ ∘ φ, begin
  intros x y,
  dsimp,
  rw map_op,
  rw map_op
end⟩

infixr ` ∘* `:90 := hom.comp

@[simp, to_additive]
lemma comp_app [hom_class Φ G H] [hom_class Ψ H K] (ψ : Ψ) (φ : Φ) (a : G) :
(ψ ∘* φ) a = ψ (φ a) := rfl

@[simp, to_additive]
lemma comp_app' [hom_class Φ G H] [hom_class Ψ H K] (ψ : Ψ) (φ : Φ) (a : G) :
(ψ ∘* φ).to_fun a = ψ (φ a) := rfl

@[simp, to_additive]
lemma comp_assoc [hom_class Φ G H] [hom_class Ψ H K] [hom_class Χ K L]
(χ : Χ) (ψ : Ψ) (φ : Φ) :
χ ∘* (ψ ∘* φ) = (χ ∘* ψ) ∘* φ := rfl

@[to_additive]
def mono_comp [mono_class Φ G H] [mono_class Ψ H K] (ψ : Ψ) (φ : Φ) : G ↪* K :=
⟨ψ ∘* φ, λ x y h, mono_inj φ (mono_inj ψ h)⟩

@[to_additive]
def epi_comp [epi_class Φ G H] [epi_class Ψ H K] (ψ : Ψ) (φ : Φ) : G ↠* K :=
⟨ψ ∘* φ, begin
  intro x,
  obtain ⟨a, ha⟩ := epi_surj ψ x,
  obtain ⟨b, hb⟩ := epi_surj φ a,
  refine ⟨b, _⟩,
  simp,
  rw [hb, ha]
end⟩

@[to_additive]
def iso_comp [iso_class Φ G H] [iso_class Ψ H K] (ψ : Ψ) (φ : Φ) : G ≅ K

-- Common homomorphisms

@[to_additive]
def trivial_hom (G H : Type*) [group G] [group H] : G →* H :=
⟨λ x, 1, λ x y, by rw one_mul⟩

@[to_additive]
def iso_self (G : Type*) [group G] : G ≅ G :=
⟨⟨id, λ a b, rfl⟩, λ φ a, id, λ g, ⟨g, rfl⟩⟩

@[to_additive]
def inclusion_mono {G : Type*} [group G] (H : subgroup G) : H.carrier ↪* G :=
⟨⟨λ x, x, λ x y, rfl⟩, begin
  intros x y h,
  dsimp at h,
  ext,
  exact h
end⟩

-- Isomorphism is an equivalence relation

@[to_additive]
noncomputable def iso_symm [iso_class Φ G H] (φ : Φ) : H ≅ G :=
⟨⟨function.surj_inv (iso_class.bij φ).2,
begin
  intros x y,
  apply (iso_class.bij φ).1,
  rw map_op,
  repeat { rw function.surj_inv_eq (iso_class.bij φ).2 }
end⟩,
begin
  intros x y h,
  dsimp at h,
  have : φ (function.surj_inv _ x) = φ (function.surj_inv _ y) := by rw h,
  repeat { rwa function.surj_inv_eq (iso_class.bij φ).2 at this },
end,
begin
  intro x,
  refine ⟨φ x, _⟩,
  dsimp,
  apply function.left_inverse_surj_inv
end⟩

@[to_additive]
def iso_trans [iso_class Φ G H] [iso_class Ψ H K] (φ : Φ) (ψ : Ψ) : G ≅ K :=


end hom

end notes
