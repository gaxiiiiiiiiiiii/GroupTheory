import Yukie.Hom

namespace GroupTheory

namespace LeftQuotient

def leftRel {G} [Group G] (H : Subgroup G) : Setoid G where
  r a b := a⁻¹ * b ∈ H
  iseqv := {
    refl := by simp; apply Subgroup.one_mem
    symm := by
      intro x y Hxy
      apply Subgroup.inv_mem_iff.1
      rw [mul_inv_rev, inv_inv]
      exact Hxy
    trans := by
      intro x y z Hx Hy
      rw [<- mul_one x⁻¹, <- mul_inv_self y, <- mul_assoc, mul_assoc _ _ z]
      apply (Subgroup.mul_mem Hx Hy)
  }


def leftQuotient (G) [Group G] (H : Subgroup G) :=
  Quotient (leftRel H)

infix:35 " ⧸ " => leftQuotient

variable [Group G] {H : Subgroup G}

@[reducible]
def mk (a : G) : G ⧸ H := Quotient.mk'' a

theorem lift_bij : Function.Surjective (LeftQuotient.mk (H := H)) := by
  rintro ⟨x⟩; exists x



notation:80 a:80 " ⋆ " H:81 => (mk a : _ ⧸ H)


@[simp]
theorem leftRel_apply {a b : G} : (leftRel H).r a b ↔ a ⁻¹ * b ∈ H := Iff.rfl

theorem eq' {a b : G} : a ⋆ H = b ⋆ H ↔ (leftRel H).r a b := by
  constructor<;> intro H
  · apply Quotient.exact H
  · apply Quotient.sound' H

@[simp]
theorem eq {a b : G} : a ⋆ H = b ⋆ H ↔ a⁻¹ * b ∈ H :=
  eq'.trans leftRel_apply

@[simp]
theorem mk_eq : (Quot.mk _ a : G ⧸ H) = a ⋆ H := rfl



def lift {Y} (f : G → Y)
    (h : ∀ a b : G, a⁻¹ * b ∈ H → f a = f b) : G ⧸ H → Y :=
  Quotient.lift f h


@[simp]
theorem lift_mk (f : G → Y) (h) (a : G) : (lift f h) (a ⋆ H) = f a := rfl



end LeftQuotient

-- namespace RightQuotient

-- def rightRel {G} [Group G] (H : Subgroup G) : Setoid G where
--   r a b := b * a⁻¹ ∈ H
--   iseqv := {
--     refl := by simp; apply Subgroup.one_mem
--     symm := by
--       intro x y Hxy
--       rw [<- inv_inv x, <- mul_inv_rev]
--       apply Subgroup.inv_mem; assumption
--     trans := by
--       intro x y z H1 H2
--       rw [<- mul_one z, <- inv_mul_self y, <- mul_assoc, mul_assoc _ y]
--       apply Subgroup.mul_mem<;> assumption
--   }

-- def rightQuotient (G) [Group G] (H : Subgroup G) :=
--   Quotient (rightRel H)

-- notation:35 H "⧹" G => rightQuotient G H

-- variable [Group G] {H : Subgroup G}


-- @[reducible]
-- def mk (a : G) : H ⧹ G := Quotient.mk'' a


-- notation:80 a:80 " ⋆ " H:81 => (mk a : H ⧹ _)


-- @[simp]
-- theorem leftRel_apply {a b : G} : (rightRel H).r a b ↔ b * a⁻¹ ∈ H := Iff.rfl


-- theorem eq' {a b : G} : (a ⋆ H : H ⧹ G) = (b ⋆ H : (H ⧹ G)) ↔ (rightRel H).r a b := by
--   constructor<;> intro H
--   · apply Quotient.exact H
--   · apply Quotient.sound' H

-- @[simp]
-- theorem eq {a b : G} : mk (H := H) a = mk b ↔ b * a⁻¹ ∈ H := by
--   apply eq'.trans; simp



-- -- @[simp]
-- -- theorem mk_eq : (Quot.mk _ a : G ⧸ H) = (a ⋆ H : H ⧹ G) := rfl



-- def lift {Y} (f : G → Y)
--     (h : ∀ a b : G, b * a ⁻¹ ∈ H → f a = f b) : (H ⧹ G) → Y := by
--     apply Quotient.lift f
--     unfold HasEquiv.Equiv instHasEquiv; simp
--     apply h


-- @[simp]
-- theorem lift_mk (f : G → Y) (h) (a : G) : (RightQuotient.lift f h) (a ⋆ H) = f a := rfl


-- end RightQuotient

end GroupTheory
