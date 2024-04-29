-- import Yukie.Quotient
import Yukie.Subgroup
import Yukie.Hom
import Yukie.Quotient



namespace GroupTheory

class Normal {G} [Group G] (H : Subgroup G) where
  conj_mem : ∀ (g: G), ∀ h ∈ H,  g * h * g⁻¹ ∈ H


theorem mem_comm {G} [Group G] {H : Subgroup G} [Normal H] {a b : G} : a * b ∈ H -> b * a ∈ H := by
  intro Hab
  rw [<- mul_one a, <- mul_inv_self b, <- mul_assoc a, <- mul_assoc b]
  apply (Normal.conj_mem _ _ Hab)

theorem abelian_normal {G} [Group G] (H : Subgroup G) :
    Abelian G -> Normal H := by
  intro H0; constructor; intro  g h Hh
  rw  [Abelian.mul_comm g h, mul_assoc]; simp
  assumption


def ker_normal [Group G₁] [Group G₂] (f : G₁ →* G₂) : Normal f.ker := by
  constructor; intro g h Hh; simp at *
  rw [Hh, map_inv]; simp




theorem normal_MUL_comm [Group G] {N : Subgroup G} [Normal N] {g : G} :  {g} * (↑N : Set G)  = (N : Set G) * {g} := by
  ext x; simp
  constructor<;> intro ⟨a, Ha, Hx⟩
  · rw [Hx]
    exists g * a * g⁻¹; simp
    apply Normal.conj_mem; assumption
  · rw [Hx]
    exists g⁻¹ * a * g; constructor
    · conv => arg 1; arg 2; rw [<- inv_inv g]
      apply Normal.conj_mem; assumption
    · rw [<- mul_assoc, <- mul_assoc]; simp


instance instLeftQuotientGroup [Group G] {H : Subgroup G} [isNormal : Normal H] : Group (G ⧸ H) where
  mul := Quotient.map₂' (fun a b ↦ a * b) <| by {
    intro x y Hxy a b Hab; simp at *
    rw [<- mul_assoc]
    apply mem_comm
    rw [<- mul_assoc b, <- mul_assoc, mul_assoc _ x⁻¹]
    apply Subgroup.mul_mem
    · apply mem_comm; assumption
    · assumption
  }
  one := 1 ⋆ H
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; dsimp
    rw [mul_assoc]
  one_mul := by rintro ⟨a⟩; dsimp; rw [one_mul]
  inv :=
    LeftQuotient.lift (fun a ↦ a⁻¹ ⋆ H) <| by {
    intro a b  Hab; simp at *
    rw [<- inv_inv a, <- mul_inv_rev]
    apply H.inv_mem
    apply mem_comm Hab
  }
  mul_inv_left := by
    rintro ⟨g⟩; dsimp
    rw [inv_mul_self]

@[simp]
theorem mk_mul  [Group G] {H : Subgroup G} [Normal H] (a b : G) : (a * b) ⋆ H = a ⋆ H  * b ⋆ H := by
  apply Quotient.sound; simp
  unfold HasEquiv.Equiv instHasEquiv; simp
  rw [<- mul_assoc, mul_assoc _ _ a]; simp
  apply Subgroup.one_mem



instance [Group G] [Group H] (f : G →* H) : Group (G ⧸ f.ker) :=
  instLeftQuotientGroup (isNormal := ker_normal f)


def mk_hom [Group G] (N : Subgroup G) [Normal N] : G →* G ⧸ N where
  toFun := LeftQuotient.mk
  map_mul' := by intro a b; rfl

@[simp]
theorem mk_hom_apply [Group G] {N : Subgroup G} [Normal N] (g : G) : mk_hom N g = (g ⋆ N : G ⧸ N) := rfl


theorem ker_mk [Group G] {N : Subgroup G} [Normal N] : (mk_hom N).ker = N := by
  ext x
  unfold GroupHom.ker; simp
  unfold OfNat.ofNat One.toOfNat1; simp
  unfold One.one instOne; simp
  unfold Group.one instLeftQuotientGroup; simp
  constructor<;> intro Hx
  · rw [<- inv_inv x]
    apply Subgroup.inv_mem; assumption
  · apply Subgroup.inv_mem; assumption



end GroupTheory
