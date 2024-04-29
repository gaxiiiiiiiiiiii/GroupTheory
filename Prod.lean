import Yukie.Subgroup
import Yukie.Normal
import Yukie.Hom

namespace GroupTheory


instance [Group G₁] [Group G₂] : Group (G₁ × G₂) where
  mul := λ ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ => (a₁ * b₁, a₂ * b₂)
  one := (1, 1)
  inv := λ ⟨a₁, a₂⟩ => (a₁⁻¹, a₂⁻¹)

  mul_assoc := by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
    simp; constructor<;> apply mul_assoc
  one_mul := by intro ⟨a₁, a₂⟩; simp
  mul_inv_left := by intro ⟨a₁, a₂⟩; simp

theorem hoge [Group G] {H K : Subgroup G} (HK1 : ↑H ∩ ↑K = {1}) (HKG : MUL (↑H) (K.carrier) = Set.univ) : (H × K) ≅* G where
  toFun := by intro ⟨h, k⟩; exact h * k
  map_mul' := by
    intro ⟨h₁, k₁⟩ ⟨h₂, k₂⟩; simp
    unfold HMul.hMul instHMul Mul.mul instMul Group.mul; simp
    unfold instGroupSubtypeMemSubgroupInstMembershipInstSetLikeSubgroup; simp
    unfold Subtype.val; simp
