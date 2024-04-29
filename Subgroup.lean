import Yukie.Group

namespace GroupTheory


section Subgroup

theorem subgroup_iff_mul_inv [Group G](H : Set G) :
    (∀ a b, a ∈ H -> b ∈ H -> a * b ∈ H) ∧ (∀ a, a ∈ H -> a⁻¹ ∈ H ) ↔
    (∀ a b, a ∈ H -> b ∈ H -> a * b⁻¹ ∈ H) := by
  constructor<;> intro H'
  · intro a b Ha Hb
    apply H'.1; assumption
    apply H'.2; assumption
  · constructor
    · intro a b Ha Hb
      rw [<- inv_inv b]
      apply H'; assumption
      rw [<- one_mul b⁻¹]
      apply H'<;> try assumption
      rw [<- mul_inv_self a]
      apply H'<;> assumption
    · intro a Ha
      rw [<- one_mul a⁻¹]
      apply H'<;> try assumption
      rw [<- mul_inv_self a]
      apply H'<;> assumption

@[ext]
structure Subgroup (G) [Group G] where
  carrier : Set G
  one_mem' : (1 : G) ∈ carrier
  mul_mem' : ∀ {a b}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_mem' : ∀ {a}, a ∈ carrier → a⁻¹ ∈ carrier


variable [Group G] {H : Subgroup G}

instance : SetLike (Subgroup G) G where
  coe h := h.carrier
  coe_injective' H₁ H₂ E := by apply Subgroup.ext; apply E

theorem Subgroup.one_mem : (1 : G) ∈ H := H.one_mem'
theorem Subgroup.mul_mem {a b : G} : a ∈ H → b ∈ H → a * b ∈ H := H.mul_mem'
theorem Subgroup.inv_mem {a : G} : a ∈ H → a⁻¹ ∈ H := H.inv_mem'
theorem Subgroup.inv_mem_iff {a : G} : a⁻¹ ∈ H ↔ a ∈ H := by
  constructor<;> intro H'
  · rw [← inv_inv a]; apply Subgroup.inv_mem H'
  · apply Subgroup.inv_mem H'


instance : Group H where
  mul := fun a b => by use (a.1 * b.1); apply H.mul_mem a.2 b.2
  one := by use 1; apply H.one_mem
  inv a := by use a⁻¹; apply H.inv_mem a.2
  mul_assoc a b c := by simp; rw [mul_assoc]
  one_mul := by simp
  mul_inv_left a := by simp

theorem Subgroup.pow_mem (x : G) : x ∈ H -> ∀ n, Pow x n ∈ H := by
  intro Hx n
  induction n with
  | ofNat n =>
    rw [Pow_ofNat]
    induction n with
    | zero => simp; apply H.one_mem
    | succ n IH =>
      simp; apply H.mul_mem<;> assumption
  | negSucc n =>
    rw [Pow_negSucc]; simp
    apply Subgroup.mul_mem; apply Subgroup.inv_mem; assumption
    induction n with
    | zero => simp; apply H.one_mem
    | succ n IH =>
      simp; apply H.mul_mem<;> try assumption
      apply H.inv_mem; assumption

instance : Top (Subgroup G) where
  top := {
    carrier := Set.univ
    one_mem' := by simp
    mul_mem' := by  simp
    inv_mem' := by simp
  }

theorem top_mem (a : G) : a ∈ (⊤ : Subgroup G) := by trivial

instance : Bot (Subgroup G) where
  bot := {
    carrier := {1}
    one_mem' := by simp
    mul_mem' := by simp
    inv_mem' := by simp
  }

theorem bot_mem (a : G) : a ∈ (⊥ : Subgroup G) ↔ a = 1 := by trivial




-- def center : Subgroup G where
--   carrier := {a : G| ∀ b, a * b = b * a}
--   one_mem' := by simp
--   mul_mem' := by
--     intro a b Ha Hb c; simp at *
--     rw [mul_assoc, Hb c, <- mul_assoc, Ha c, mul_assoc]
--   inv_mem' := by
--     intro a Ha b; simp at *
--     apply mul_left_cancel a
--     rw [<- mul_assoc a, mul_inv_self, one_mul, <- mul_assoc, Ha b, mul_assoc, mul_inv_self, mul_one]

-- def Subgroup.centralizer : Subgroup G where
--   carrier := { a : G | ∀ x ∈ H, a * x = x * a }
--   one_mem' := by simp
--   mul_mem' := by
--     intro a b Ha Hb x Hx; simp at *
--     rw [mul_assoc, Hb x Hx, <- mul_assoc, Ha x Hx, mul_assoc]
--   inv_mem' := by
--     intro a Ha x Hx; simp at *
--     apply mul_left_cancel a
--     rw [<- mul_assoc, mul_inv_self, one_mul, <- mul_assoc, Ha x Hx, mul_assoc, mul_inv_self, mul_one]

-- def Subgroup.normalizer : Subgroup G where
--   carrier := { a : G | ∀ x, x ∈ H ↔ a * x * a⁻¹ ∈ H }
--   one_mem' := by simp
--   mul_mem' := by
--     intro a b Ha Hb x; simp at *
--     rw [mul_assoc, mul_assoc, <- mul_assoc x, <- mul_assoc b, <- mul_assoc b, <- mul_assoc a]
--     constructor<;> intro Hx
--     · apply (Ha _).1
--       apply (Hb x).1
--       exact Hx
--     · apply (Ha _).2 at Hx
--       apply (Hb x).2 Hx
--   inv_mem' := by
--     intro a Ha x; simp at *
--     have H0 := (Ha (a⁻¹ * x * a))
--     conv at H0 =>
--       rhs
--       rw [mul_assoc, mul_assoc, mul_inv_self, mul_one]
--       rw [<- mul_assoc, mul_inv_self, one_mul]
--     constructor<;> intro Hx
--     · apply H0.2 Hx
--     · apply H0.1 Hx


-- def normalSubgroup (x : G) : Subgroup G where
--   carrier := {x * a * x⁻¹ | a : G}
--   one_mem' := by
--     simp
--     use (x⁻¹ * x)
--     rw [<- mul_assoc]
--     simp
--   mul_mem' := by
--     intro a b ⟨a', Ha'⟩ ⟨b', Hb'⟩
--     simp at *
--     rw [<- Ha', <- Hb']
--     rw [mul_assoc, <- mul_assoc x⁻¹, <- mul_assoc x⁻¹]
--     simp
--     use (a' * b')
--     rw [<- mul_assoc, mul_assoc _ _ x⁻¹]
--   inv_mem' := by
--     intro a ⟨a', Ha'⟩
--     rw [<- Ha']
--     simp
--     use a'⁻¹
--     rw [mul_assoc]

def iterSubgroup (H1 H2 : Subgroup G) : Subgroup G where
  carrier := H1 ∩ H2
  one_mem' := by
    simp
    constructor
    · apply H1.one_mem
    · apply H2.one_mem
  mul_mem' := by
    intro a b ⟨Ha1, Ha2⟩ ⟨Hb1, Hb2⟩
    simp at *
    constructor
    · apply H1.mul_mem Ha1 Hb1
    · apply H2.mul_mem Ha2 Hb2
  inv_mem' := by
    intro a ⟨Ha1, Ha2⟩
    simp at *
    constructor
    · apply H1.inv_mem Ha1
    · apply H2.inv_mem Ha2

@[simp]
theorem iterSubgroup_mem (H1 H2 : Subgroup G) (a : G) : a ∈ iterSubgroup H1 H2 ↔ a ∈ H1 ∧ a ∈ H2 := by
  unfold iterSubgroup
  constructor<;> intro H
  · simp at H
    constructor
    · apply H.1
    · apply H.2
  · constructor
    · apply H.1
    · apply H.2

def closure (S : Set G) : Subgroup G where
  carrier := fun g => ∀ H : Subgroup G, S ⊆ ↑H -> g ∈ H
  one_mem' := by
    intro X _
    apply X.one_mem
  mul_mem' := by
    intro a b Ha Hb X HX
    apply X.mul_mem
    · apply Ha; assumption
    · apply Hb; assumption
  inv_mem' := by
    intro a Ha X HX
    apply X.inv_mem
    apply Ha; assumption



notation "{|" S "|}" => closure S

@[simp]
theorem closure_mem (S : Set G) (x : G) : x ∈ ↑{|S|} ↔ (∀ H : Subgroup G, S ⊆ H -> x ∈ H) := Iff.rfl



def cyclic (a : G) : Subgroup G := {|{a}|}

def cyclic' (a : G) : Subgroup G where
  carrier := {g | ∃ n, g = Pow a n}
  one_mem' := by
    simp; use 0
    unfold Pow; simp
  mul_mem' := by
    intro x y ⟨n, Hn⟩ ⟨m, Hm⟩; simp
    use (n + m)
    rw [Hn, Hm, Pow_add]
  inv_mem' := by
    intro x ⟨n, Hn⟩; simp
    use (-n)
    rw [Hn, Pow_neg, Pow_inv]

@[simp]
theorem cyclic'_mem (a x : G) : x ∈ cyclic' a ↔ ∃ n, x = Pow a n := Iff.rfl

theorem cyclic'_self_mem (a : G) : a ∈ cyclic' a := by
  use 1; simp


@[simp]
theorem cyclic_eq (a : G) : cyclic a = cyclic' a := by
  ext x
  unfold cyclic cyclic'; simp
  unfold closure; simp
  constructor<;> intro Hx <;> simp at *
  · change (∀ H, a ∈ H → x ∈ H) at Hx
    apply Hx (cyclic' a)
    apply cyclic'_self_mem
  · rcases Hx with ⟨n, Hn⟩; subst x
    intro S Sa
    cases n
    case ofNat n =>
      rw [Pow_ofNat]
      induction n with
      | zero =>
        simp; apply Subgroup.one_mem
      | succ n IH =>
        simp; apply Subgroup.mul_mem<;> assumption
    case negSucc n =>
      rw [Pow_negSucc]; simp
      apply Subgroup.mul_mem
      · apply Subgroup.inv_mem; assumption
      · induction n with
        | zero => simp; apply Subgroup.one_mem
        | succ n IH =>
          simp; apply Subgroup.mul_mem<;> try assumption
          apply Subgroup.inv_mem; assumption


@[simp]
theorem cyclic_mem (a b : G) : b ∈ cyclic a ↔ ∃ n, b = Pow a n := by simp


theorem closure_preserve_inclusion (S₁ S₂ : Set G) :
    S₁ ⊆ S₂ -> ↑({| S₁ |} : Set G) ⊆  ↑{| S₂ |} := by
  intro H0 x Hx; simp at *
  intro H SH; apply Hx
  intro y Hy; apply SH
  apply H0; assumption


theorem syclic_abelian (a : G) : Abelian (cyclic a) := by
  constructor; simp; intro x n Hx y m Hy
  unfold HMul.hMul instHMul; simp
  unfold Mul.mul instMul; simp
  unfold Group.mul instGroupSubtypeMemSubgroupInstMembershipInstSetLikeSubgroup; simp
  rw [Hx, Hy]
  rw [<- Pow_add, <- Pow_add, Int.add_comm]

end Subgroup

section MUL

variable [Group G] {H K  : Subgroup G}

  def MUL (A B : Set G) := { g : G | ∃ a ∈ A, ∃ b ∈ B, g = a * b }
  def INV (A : Set G) := { g : G | ∃ a ∈ A, g = a⁻¹ }

  instance : Mul (Set G) := ⟨MUL⟩
  instance : Inv (Set G) := ⟨INV⟩

  @[simp]
  theorem MUL_mem (A B : Set G) (g : G) : g ∈ A * B ↔ ∃ a ∈ A, ∃ b ∈ B, g = a * b := Iff.rfl

  @[simp]
  theorem INV_mem (A : Set G) (g : G) : g ∈ A⁻¹ ↔ ∃ a ∈ A, g = a⁻¹ := Iff.rfl

  theorem MUL_assoc (A B C : Set G) : A * B * C = A * (B * C) := by
    ext x; simp
    constructor<;> intro H
    · rcases H with ⟨ab, ⟨a, Ha, b, Hb, Hab⟩, c, Hc, Hx⟩
      use a; constructor; assumption
      use (b * c); constructor
      · use b; constructor; assumption
        use c
      · rw [Hx, Hab, mul_assoc]
    · rcases H with ⟨a, Ha, bc, ⟨b, Hb, c, Hc, Hbc⟩, Hx⟩
      use (a * b); constructor
      · use a; constructor; assumption
        use b
      · use c; constructor; assumption
        rw [Hx, Hbc, mul_assoc]

  theorem INV_INV (A : Set G) : A⁻¹⁻¹ = A := by
    ext x; simp
    constructor<;> intro H
    · rcases H with ⟨a, ⟨a', Ha', Ha⟩, Hx⟩
      rw [Hx, Ha, inv_inv]; assumption
    · use (x⁻¹); constructor
      · use x
      · rw [inv_inv]

  theorem MUL_INV_rev (A B : Set G) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
    ext x; simp
    constructor<;> intro H
    · rcases H with ⟨x', ⟨a, Ha, b, Hb, Hab⟩, Hx⟩
      use b⁻¹; constructor; use b
      use a⁻¹; constructor; use a
      rw [Hx, Hab, mul_inv_rev]
    · rcases H with ⟨b, ⟨b', Hb', Hb⟩, a, ⟨a',Ha', Ha⟩, Hx⟩
      rw [Hx, Ha, Hb]; clear Hx Ha Hb
      use (a' * b')
      constructor
      · use a'; constructor; assumption
        use b'
      · rw [mul_inv_rev]

  theorem MUL_INV_iff_mul_inv (H : Set G) :
      H * H⁻¹ ⊆ H ↔ (∀ a b, a ∈ H -> b ∈ H -> a * b⁻¹ ∈ H) := by
    constructor<;> intro H'
    · intro a b Ha Hb; apply H'; simp
      use a; constructor; assumption
      use b⁻¹; constructor
      use b
      simp
    · intro x Hx; simp at *
      rcases Hx with ⟨a, Ha, b', ⟨b, Hb, Hb'⟩, Hx⟩
      rw [Hx, Hb']
      apply H'<;> assumption

  theorem MUL_iff_mul (H : Set G) :
      H * H ⊆ H ↔ (∀ a b, a ∈ H -> b ∈ H -> a * b ∈ H) := by
    constructor<;> intro H'
    · intro a b Ha Hb; apply H'; simp
      use a; constructor; assumption
      use b
    · intro x Hx; simp at *
      rcases Hx with ⟨a, Ha, b, Hb, Hx⟩
      rw [Hx]
      apply H'<;> assumption

  theorem INV_iff_inv (H : Set G) :
      H⁻¹ ⊆ H ↔ (∀ a, a ∈ H -> a⁻¹ ∈ H) := by
    constructor<;> intro H'
    · intro a Ha; apply H'; simp
      use a
    · intro x Hx; simp at *
      rcases Hx with ⟨a, Ha, Hx⟩
      rw [Hx]
      apply H'; assumption

  def interSubgroup [Group G] (H K  : Subgroup G) : Subgroup G where
    carrier := H ∩ K
    one_mem' := by simp; constructor<;> apply Subgroup.one_mem
    mul_mem' := by
      intro a b ⟨Ha, Ka⟩ ⟨Hb, Kb⟩; simp at *
      constructor<;> apply Subgroup.mul_mem<;> assumption
    inv_mem' := by
      intro a ⟨Ha, Ka⟩; simp at *
      constructor<;> apply Subgroup.inv_mem<;> assumption

   def interSubgroupL (H K : Subgroup G): Subgroup H where
      carrier := {h | h.val ∈ K}
      one_mem' := Subgroup.one_mem
      mul_mem' := by
        intro a b Ha Hb; simp
        rcases a with ⟨x, Hx⟩
        rcases b with ⟨y, Hy⟩
        simp at *
        change x * y ∈ K
        apply Subgroup.mul_mem<;> assumption
      inv_mem' := by
        intro a Ha
        rcases a with ⟨x, Hx⟩; simp at *
        change x⁻¹ ∈ K
        apply Subgroup.inv_mem; assumption

  @[simp]
  theorem interSubgroup_mem [Group G] {H K  : Subgroup G} (g : G) : g ∈ interSubgroup H K ↔ g ∈ H ∧ g ∈ K := by
    unfold interSubgroup
    constructor<;> intro ⟨Hl,Hr⟩<;> constructor<;> assumption

  @[simp]
  theorem interSubgroupL_mem [Group G] {H K  : Subgroup G} (h : H) : h ∈ interSubgroupL H K ↔ h.val ∈ K := by
    apply Iff.rfl

  

  -- theorem interSubgroup_normal : Normal (interSubgroupL H K) := by
  --   constructor; intro ⟨h, Hh⟩ ⟨k, Hk⟩ Kk; simp at *
  --   change h * k * h⁻¹ ∈ K
  --   apply Normal.conj_mem; assumption

end MUL

end GroupTheory
