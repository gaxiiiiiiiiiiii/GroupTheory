import Yukie.Hom
import Yukie.Quotient
import Yukie.Normal

namespace GroupTheory
open GroupHom
open LeftQuotient


theorem first_isomorphism_theorem [Group G] [Group H] (f : G →* H) : (G ⧸ ker f) ≅* range f where
  toFun := by
    rintro a
    have h : ∀ (a b : G), a⁻¹ * b ∈ f.ker → f a = f b := by
      simp; intro a b Hab
      apply mul_left_cancel (f a⁻¹)
      rw [Hab, map_inv]; simp
    simp
    exists (lift f h a)
    rcases Quot.exists_rep a with ⟨g, Hg⟩
    rw [<- Hg]; simp
  map_mul' := by
    rintro ⟨a⟩ ⟨b⟩; simp
    ext; simp
    rw [<- @mk_mul G _ f.ker (ker_normal f) a b]; simp
    rfl
  injective := by
    rintro ⟨a⟩ ⟨b⟩ h; simp at *
    rw [<- h, map_inv]; simp
  surjective := by
    rintro ⟨a, Ha⟩; simp at *
    apply mem_range.1 at Ha
    rcases Ha with ⟨g, Hg⟩
    exists (g ⋆ f.ker)




-- theorem hoge [Group G] {N : Subgroup G} [Normal N] : (Subgroup (G ⧸ N)) ≃ { H // ↑N ⊆ ↑H } where
--   toFun H := sorry
--   invFun K := sorry
--   left_inv := sorry
--   right_inv := sorry


section hoge
  variable [Group G] {H N : Subgroup G} [Normal N]

  theorem MUL_comm : (H * N : Set G) = (N * H) := by
    ext x; simp; constructor<;> intro Hx
    · rcases Hx with ⟨a, Ha, b, Hb, Hab⟩
      exists a * b * a⁻¹; constructor
      · apply Normal.conj_mem; assumption
      exists a; constructor; assumption; simp
      assumption
    · rcases Hx with ⟨a, Ha, b, Hb, Hab⟩
      exists b; constructor; assumption
      exists (b⁻¹ * a * b⁻¹⁻¹); constructor
      · apply Normal.conj_mem; assumption
      simp; rw [<- mul_assoc, <- mul_assoc]; simp; assumption

  def MUL_group : Subgroup G where
    carrier := H * N
    one_mem' := by
      simp
      exists 1; constructor; apply H.one_mem
      exists 1; constructor; apply N.one_mem
      simp
    mul_mem' := by
      intro a b Ha hb
      rcases Ha with ⟨h₁, Hh₁, n₁, Nn₁, Ha⟩
      rcases hb with ⟨h₂, Hh₂, n₂, Nn₂, Hb⟩
      have NH : n₁ * h₂ ∈ N * (H : Set G) := by
        simp; exists n₁; constructor; assumption; exists h₂
      rw [<- MUL_comm] at NH
      rcases NH with ⟨h, Hh, n, Nn, HN⟩
      exists (h₁ * h); constructor; apply H.mul_mem<;> assumption
      exists (n * n₂); constructor; apply N.mul_mem<;> assumption
      rw [<- mul_assoc, mul_assoc _ h, <- HN, <- mul_assoc, mul_assoc _ _ n₂, Ha, Hb]
    inv_mem' := by
      intro a ⟨h, Hh, n, Nn, Ha⟩
      rw [Ha, MUL_comm]; simp
      exists n⁻¹; constructor; apply N.inv_mem; assumption
      exists h⁻¹; constructor; apply H.inv_mem; assumption
      rfl

  def interSubgroupL_normal : Normal (interSubgroupL H N) := by
    constructor; intro ⟨h, Hh⟩ ⟨k, Hk⟩ Kk; simp at *
    change h * k * h⁻¹ ∈ N
    apply Normal.conj_mem; assumption

  instance : Group  (H ⧸ interSubgroupL H N) :=
    instLeftQuotientGroup (isNormal := interSubgroupL_normal)






  
