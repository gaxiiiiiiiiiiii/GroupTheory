import Yukie.Subgroup

namespace GroupTheory

@[ext]
structure GroupHom (G₁ G₂ : Type) [Group G₁] [Group G₂] where
  toFun : G₁ → G₂
  map_mul' : ∀ a b, toFun (a * b) = toFun a * toFun b

infixr:25 "→*" => GroupHom

@[ext]
structure GroupIso (G) [Group G] (H) [Group H] extends G →* H where
  injective : toFun.Injective
  surjective : toFun.Surjective

infixr:25 " ≅* " => GroupIso

theorem iso_leftinverse {G} [Group G] {H} [Group H] (f : G ≅* H) : Function.LeftInverse (Function.invFun f.toFun) f.toFun := by
  apply Function.leftInverse_invFun f.2

theorem iso_rightinverse {G} [Group G] {H} [Group H] (f : G ≅* H) : Function.RightInverse (Function.invFun f.toFun) f.toFun := by
  apply Function.rightInverse_invFun f.3

noncomputable def iso_invFun_hom [Group G₁] [Group G₂] (f : G₁ ≅* G₂) : G₂ →* G₁ where
  toFun := Function.invFun f.toFun
  map_mul' := by
    intro a b
    apply f.injective
    rw [f.map_mul', iso_rightinverse f, iso_rightinverse f, iso_rightinverse f]

variable [Group G₁] [Group G₂] {f : G₁ →* G₂}

instance : FunLike (G₁ →* G₂)  G₁ G₂ where
  coe := fun f => f.toFun
  coe_injective' f₁ f₂ E := by apply GroupHom.ext; apply E

@[simp]
theorem map_mul {a b : G₁} : f (a * b) = f a * f b := f.map_mul' a b

@[simp]
theorem map_one : f 1 = 1 := by
  apply mul_left_cancel (f 1)
  rw [<- map_mul, mul_one, mul_one]

theorem map_inv (a : G₁) : f a⁻¹ = (f a)⁻¹ := by
  apply mul_left_cancel (f a)
  rw [<- map_mul, mul_inv_self, mul_inv_self, map_one]

def GroupHom.comp [Group G₁] [Group G₂] [Group G₃]
  (f₂ : G₂ →* G₃) (f₁ : G₁ →* G₂) : G₁ →* G₃ where
  toFun := f₂ ∘ f₁
  map_mul' a b := by simp [map_mul, map_mul]

@[simp]
theorem GroupHom.comp_apply [Group G₁] [Group G₂] [Group G₃]
  (f₂ : G₂ →* G₃) (f₁ : G₁ →* G₂) (a : G₁) : (GroupHom.comp f₂ f₁).toFun a = f₂.toFun (f₁.toFun a) := rfl

def GroupIso.comp
    [Group G₁] [Group G₂] [Group G₃]
    (f₁ : G₁ ≅* G₂) (f₂ : G₂ ≅* G₃) : G₁ ≅* G₃ where
  toFun := f₂.toFun ∘ f₁.toFun
  map_mul' a b := by simp; rw [f₁.map_mul', f₂.map_mul']
  injective := by
    intro a b H; simp at *
    apply f₁.injective
    apply f₂.injective
    apply H
  surjective := by
    intro a; simp at *
    rcases (f₂.surjective a) with ⟨b, Hb⟩
    rcases (f₁.surjective b) with ⟨c, Hc⟩
    exists c; rw [Hc, Hb]
@[simp]
theorem GroupIso.comp_apply
    [Group G₁] [Group G₂] [Group G₃]
    (f₁ : G₁ ≅* G₂) (f₂ : G₂ ≅* G₃) (a ) : (GroupIso.comp  f₁ f₂).toFun a = f₂.toFun (f₁.toFun a) := rfl

def GroupHom.id (G) [Group G] : G →* G where
  toFun := fun x => x
  map_mul' a b := by simp


def GroupHom.one : G₁ →* G₂ where
  toFun := fun _ => 1
  map_mul' := by simp

namespace GroupHom


def range (f : G₁ →* G₂) : Subgroup G₂ where
  carrier := Set.range f
  one_mem' := by simp; use 1; apply map_one
  mul_mem' := by
    simp; intro a b a0 Ha b0 Hb
    use (a0 * b0)
    rw [map_mul, Ha, Hb]
  inv_mem' := by
    simp; intro x; use x⁻¹; rw [map_inv]

def ker (f : G₁ →* G₂) : Subgroup G₁ where
  carrier := { x | f x = 1}
  one_mem' := by simp
  mul_mem' := by
    simp; intro a b Ha Hb
    rw [Ha, Hb, one_mul]
  inv_mem' := by
    simp; intro x Hx
    rw [map_inv, Hx, inv_one]

@[simp]
theorem mem_ker {f : G₁ →* G₂} {a : G₁} : a ∈ f.ker ↔ f a = 1 := Iff.rfl

@[simp]
theorem mem_range {f : G₁ →* G₂} {b : G₂} : b ∈ f.range ↔ ∃ a, f a = b := Iff.rfl


theorem hom_inj_iff_ker_bot  : Function.Injective f ↔ f.ker = ⊥ := by
  constructor<;> intro H
  · ext x
    change f x = 1 ↔ x = 1
    constructor<;> intro Hx; simp at *
    · apply H; rw [Hx, map_one]
    · rw [Hx, map_one]
  · intro a b Hab
    apply mul_right_cancel b⁻¹; simp
    have Hf: (a * b⁻¹) ∈ ker f := by
      simp; rw [Hab, map_inv]; simp
    rw [H] at Hf
    assumption

theorem hom_sur_iff_rang_top : Function.Surjective f ↔ f.range = ⊤ := by
  constructor<;> intro H
  · ext x
    constructor<;> intro _; simp at *
    · change x ∈ Set.univ; simp
    · change ∃ a, f a = x
      rcases H x with ⟨a, Ha⟩
      use a
  · intro x
    have : x ∈ range f := by
      rw [H]; change x ∈ Set.univ; simp
    assumption


noncomputable instance Aut (G) [Group G]: Group (G ≅* G) where
  one := by
    constructor
    case toGroupHom => exact GroupHom.id G
    case injective => intro a b Hab; assumption
    case surjective => intro a; exists a
  mul f g := GroupIso.comp g f
  inv f := by
    constructor
    case toGroupHom => exact iso_invFun_hom f
    case injective =>
      intro a b Hab
      change Function.invFun f.toFun a = Function.invFun f.toFun b at Hab
      rcases f.surjective a with ⟨a', Ha⟩
      rcases f.surjective b with ⟨b', Hb⟩
      rw [<- Ha, <- Hb, iso_leftinverse, iso_leftinverse] at Hab
      rw [<- Ha, <- Hb, Hab]
    case surjective =>
      intro a
      exists (f.toFun a)
      change Function.invFun f.toFun (f.toFun a) = a
      rw [iso_leftinverse]
  mul_assoc f g h := by
    ext x; dsimp
  one_mul f := by
    ext x; dsimp
    unfold id; simp
  mul_inv_left f := by
    simp; ext x
    unfold GroupIso.comp; simp
    unfold iso_invFun_hom; simp
    unfold id; simp
    rw [iso_leftinverse]

def inn [Group G] : G → G → G := fun g x => g * x * g⁻¹

def conj (G) [Group G]: G →* G ≅* G where
  toFun := fun g => {
    toFun := inn g
    map_mul' := by
      intros a b
      unfold inn
      conv =>
        rhs
        rw [mul_assoc _ g⁻¹, <- mul_assoc g⁻¹, <- mul_assoc g⁻¹]; simp
        rw [mul_assoc, <- mul_assoc a, <- mul_assoc]

    injective := by
      intros a b Hab; simp at *
      apply mul_left_cancel g
      apply mul_right_cancel g⁻¹
      assumption
    surjective := by
      intro x; simp; unfold inn
      exists (g⁻¹ * x * g)
      rw [<- mul_assoc, <- mul_assoc]; simp
  }
  map_mul' g₁ g₂ := by
    simp; ext x; simp
    conv =>
      lhs; unfold inn; simp
      rw [mul_assoc g₁, mul_assoc g₁, <- mul_assoc _ g₂⁻¹, <- mul_assoc]

def Inn (G) [Group G] := range (conj G)

end GroupHom

end GroupTheory
