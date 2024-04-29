import Mathlib.Tactic
import Mathlib.Data.SetLike.Basic

namespace GroupTheory

class Group (G : Type) where
  mul : G -> G -> G
  one : G
  inv : G -> G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G , mul one a = a
  mul_inv_left : ∀ a : G, mul (inv a) a = one


section Group

variable [Group G]
instance : Mul G := ⟨Group.mul⟩
instance : One G := ⟨Group.one⟩
instance : Inv G := ⟨Group.inv⟩


@[simp]
theorem one_mul (a : G) : 1 * a = a := by apply (Group.one_mul a)

@[simp]
theorem inv_mul_self (a : G) : a⁻¹ * a = 1 := by apply (Group.mul_inv_left a)

theorem mul_assoc (a b c : G) : a * b * c = a * (b * c) := by apply (Group.mul_assoc a b c)


@[simp]
theorem inv_mul_cnacel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [<- mul_assoc, inv_mul_self, one_mul]

theorem mul_left_cancel (a x y : G) : a * x = a * y -> x = y := by
  intro H
  rw [<- one_mul x, <- inv_mul_self a, mul_assoc, H, <- mul_assoc, inv_mul_self, one_mul]


@[simp]
theorem mul_one (a : G) : a * 1 = a := by
  apply mul_left_cancel a⁻¹
  rw [<- mul_assoc, inv_mul_self, one_mul]

@[simp]
theorem mul_inv_self (a : G) : a * a⁻¹ = 1 := by
  apply mul_left_cancel a⁻¹
  rw [<- mul_assoc, inv_mul_self, mul_one, one_mul]

@[simp]
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_self, one_mul]

@[simp]
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc, mul_inv_self, mul_one]

@[simp]
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul_self, mul_one]

theorem mul_right_cancel (a : G) {x y : G} : x * a = y * a → x = y := by
  intro H
  rw [<- mul_one x, <- mul_inv_self a, <- mul_assoc, H, mul_assoc, mul_inv_self, mul_one]

theorem left_inv_unique {a x : G} : x * a = 1 → a⁻¹ = x := by
  intro H
  apply mul_right_cancel a
  rw [H, inv_mul_self]

theorem right_inv_unique {a x : G} : a * x = 1 → a⁻¹ = x := by
  intro H
  apply mul_left_cancel a
  rw [H, mul_inv_self]

@[simp]
theorem inv_one : (1 : G)⁻¹ = 1 := by
  apply left_inv_unique
  rw [one_mul]

@[simp]
theorem inv_inv (a : G) : a⁻¹⁻¹ = a := by
  apply left_inv_unique
  rw [mul_inv_self]

@[simp]
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  apply left_inv_unique
  rw [mul_assoc, <- mul_assoc _ a b, inv_mul_self, one_mul, inv_mul_self]

theorem mul_inv_eq (a b c : G) : a * b⁻¹ = c <-> a = c * b := by
  constructor<;> intro H
  · rw [<- H, mul_assoc, inv_mul_self, mul_one]
  · rw [H, mul_assoc, mul_inv_self, mul_one]

theorem inv_mul_eq (a b c : G) : a⁻¹ * b = c <-> b = a * c := by
  constructor<;> intro H
  · rw [<- H, <- mul_assoc, mul_inv_self, one_mul]
  · rw [H, <- mul_assoc, inv_mul_self, one_mul]

theorem mul_inv_eq_one (a b : G) : a * b⁻¹ = 1 <-> a = b := by
  constructor<;> intro H
  · apply mul_right_cancel b⁻¹; rw [H, mul_inv_self]
  · rw [H, mul_inv_self]

theorem inv_mul_eq_one (a b : G) : a⁻¹ * b = 1 <-> a = b := by
  constructor<;> intro H
  · apply mul_left_cancel a⁻¹; rw [H, inv_mul_self]
  · rw [H, inv_mul_self]

theorem comm_inv (a b : G) : a * b = b * a → a * b⁻¹ = b⁻¹ * a := by
  intro H
  apply mul_left_cancel b
  rw [<- mul_assoc, <- mul_assoc, mul_inv_self, one_mul]
  apply mul_right_cancel b
  rw [mul_assoc, inv_mul_self, mul_one, H]

theorem mul_elim_left (a b : G) : ∀ x, a * x = b -> x = a⁻¹ * b := by
  intro x H
  rw [<- H, <- mul_assoc, inv_mul_self, one_mul]

theorem mul_elim_right (a b : G) : ∀ x, x * a = b -> x = b * a⁻¹ := by
  intro x H
  rw [<- H, mul_assoc, mul_inv_self, mul_one]

theorem inv_bijective : Function.Bijective (Group.inv : G -> G) := by
  constructor
  · intros a b H
    apply mul_left_cancel (a ⁻¹)
    change a⁻¹ = b⁻¹ at H
    rw [inv_mul_self, H, inv_mul_self]
  · intro a
    use (a⁻¹)
    change a⁻¹⁻¹ = a
    rw [inv_inv]


open Nat
open Int

def pow (a : G) (n : ℕ) : G :=
  match n with
  | 0 => 1
  | n + 1 => a * pow a n

def Pow (a : G) (n : ℤ) : G :=
  match n with
  | Int.ofNat n' => pow a n'
  | Int.negSucc n' => pow (a⁻¹) (n'+1)


@[simp]
theorem pow_zoro (a : G) : pow a 0 = 1 := rfl

@[simp]
theorem Pow_zero (a : G) : Pow a 0 = 1 := rfl



@[simp]
theorem pow_succ (a : G) (n : ℕ) : pow a (n + 1) = a * pow a n := rfl

@[simp]
theorem Pow_ofNat (a : G) n : Pow a (ofNat n) = pow a n := by
  simp [Pow]

@[simp]
theorem Pow_negSucc (a : G) n : Pow a (negSucc n) = pow (a⁻¹) (n + 1) := by
  simp [Pow]


@[simp]
theorem Pow_succ (a : G) (n : ℤ) : Pow a (n + 1) = a * Pow a n := by
  cases n with
  | ofNat n =>
    change Pow a (Int.ofNat (n + 1)) = a * Pow a (Int.ofNat n)
    rw [Pow_ofNat, Pow_ofNat]; simp
  | negSucc n =>
    cases n with
    | zero =>
      change  Pow a 0 = a * Pow a (Int.negSucc 0)
      unfold Pow; simp
    | succ n =>
      change Pow a (Int.negSucc n) = a * Pow a (Int.negSucc (succ n))
      unfold Pow; simp

theorem pow_add (a : G) (m n : ℕ) : pow a (m + n) = pow a m * pow a n := by
  induction m with
  | zero => simp
  | succ m' IH =>
    rw [succ_add]; simp
    rw [IH, mul_assoc]

theorem pow_comm (a b : G) n : a * b = b * a -> a * pow b n = pow b n * a := by
  intro H
  induction n with
  | zero => simp
  | succ n' IH =>
    simp
    rw [mul_assoc, <- IH, <- mul_assoc, <- mul_assoc, H]


theorem Pow_comm (a : G) n : a * Pow a n = Pow a n * a := by
  induction n with
  | ofNat n =>
    rw [Pow_ofNat, pow_comm]
    rfl
  | negSucc n =>
    rw [Pow_negSucc, pow_comm]
    rw [inv_mul_self, mul_inv_self]

@[simp]
theorem pow_one (a : G) : pow a 1 = a := by simp

@[simp]
theorem Pow_one (a : G) : Pow a 1 = a := by unfold Pow; simp

@[simp]
theorem one_pow (n : ℕ) : pow (1 : G) n = 1 := by
  induction n with
  | zero => simp
  | succ n' IH => simp [IH]

@[simp]
theorem one_Pow (n : ℤ) : Pow (1 : G) n = 1 := by
  cases n with
  | ofNat n => rw [Pow_ofNat]; simp
  | negSucc n => simp



theorem Pow_add_ofNat (a : G) n m : Pow a (n + ofNat m) = Pow a n * Pow a m := by
  revert n
  induction m with
  | zero => simp
  | succ m IH =>
    intro n; simp
    have : (n + (↑ m + 1)) = (n + 1) + ofNat m := by
      rw [add_assoc, add_comm 1]
      rfl
    rw [this, IH (n + 1), Pow_succ, <- mul_assoc, Pow_comm]

theorem Pow_prev (a : G) n : Pow a (n - 1) = Pow a n * a⁻¹ := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      simp
      change Pow a (negSucc 0) = a⁻¹
      rw [Pow_negSucc]; simp
    | succ n =>
      simp
      rw [Pow_comm, mul_assoc]; simp
  | negSucc n =>
    simp
    nth_rewrite 1 [pow_comm]
    rw [mul_assoc]
    rfl


theorem Pow_add_negSucc (a : G) n m : Pow a (n + negSucc m) = Pow a n * Pow (a⁻¹) (m + 1) := by
  revert n
  induction m with
  | zero =>
    intro n; simp
    induction n with
    | ofNat n =>
      cases n with
      | zero =>
        simp; unfold Pow; simp
        unfold Neg.neg instNegInt; simp
        unfold Int.neg; simp
        unfold negOfNat; simp
      | succ n =>
        simp
        rw [Pow_comm, mul_assoc]; simp
    | negSucc n =>
      simp
      have : -[n+1] + -1 = negSucc (n + 1) := by aesop
      rw [this, Pow_negSucc, pow_add, pow_add]; simp
      rw [pow_comm]; rfl
  | succ m IH =>
    simp at *
    intro n
    have : (n + -[Nat.succ m+1]) = (n  -1) + -[m +1] := by
      rw [<- neg_ofNat_succ, <- neg_ofNat_succ]; simp; ring
    rw [this, IH, Pow_prev, mul_assoc]

theorem Pow_add (a : G) n m : Pow a (n + m) = Pow a n * Pow a m := by
  cases m with
  | ofNat m => rw [Pow_add_ofNat]; rfl
  | negSucc m => rw [Pow_add_negSucc]; rfl


theorem pow_mul (a : G) (m n : ℕ) : pow a (m * n) = pow (pow a m) n := by
  revert m
  induction n with
  | zero => simp
  | succ n' IH =>
    simp; intro m
    rw [mul_succ, pow_add, IH m]
    nth_rewrite 2 [<- pow_one (pow a m)]
    rw [<- pow_add]; simp

theorem pow_inv (a : G) (n : ℕ) : pow (a⁻¹) n = (pow a n)⁻¹ := by
  induction n with
  | zero => simp
  | succ n IH =>
    simp
    rw [<- IH, pow_comm]; rfl

theorem Pow_inv (a : G) (n : ℤ) : Pow (a⁻¹) n = (Pow a n)⁻¹ := by
  cases n with
  | ofNat n => rw [Pow_ofNat, Pow_ofNat, pow_inv]
  | negSucc n => rw [Pow_negSucc, Pow_negSucc, pow_inv]


theorem Pow_neg (a : G) (n : ℤ) : Pow a (-n) = Pow (a⁻¹) n := by
  cases n with
  | ofNat n =>
    simp
    induction n with
    | zero => simp
    | succ n IH =>
      simp
      rw [Pow_add, IH]
      congr
      change Pow a (0 - 1)  = a⁻¹
      rw [Pow_prev]; simp
  | negSucc n =>
    rw [neg_negSucc, Pow_negSucc]
    change Pow a (ofNat (n +1)) = pow a⁻¹⁻¹ (n + 1)
    rw [Pow_ofNat, inv_inv]



theorem Pow_mul (a : G) (m n : ℤ) : Pow a (m * n) = Pow (Pow a m) n := by
  cases m with
  | ofNat m =>
    cases n with
    | ofNat n =>
      have : ofNat m * ofNat n = ofNat (m * n) := by rfl
      rw [this]
      rw [Pow_ofNat, Pow_ofNat, Pow_ofNat, pow_mul]
    | negSucc n =>
      simp
      rw [Pow_neg]
      change Pow a⁻¹ (ofNat (m * (n + 1))) = (Pow a (ofNat m))⁻¹ * pow (Pow a (ofNat m))⁻¹ n
      rw [Pow_ofNat, Pow_ofNat]
      rw [pow_mul, pow_succ, pow_inv]
  | negSucc m =>
    cases n with
    | ofNat n =>
      simp
      rw [Pow_neg]
      change Pow a⁻¹ (ofNat ((m + 1) * n)) = Pow (a⁻¹ * pow a⁻¹ m) (ofNat n)
      rw [Pow_ofNat, Pow_ofNat, pow_mul, pow_add]; simp
      rw [pow_comm]; rfl
    | negSucc n =>
      simp
      change Pow a (ofNat ((m + 1) *(n + 1))) = (pow a⁻¹ m)⁻¹ * a * pow ((pow a⁻¹ m)⁻¹ * a) n
      rw [Pow_ofNat, pow_mul, pow_add, pow_add]
      rw [pow_inv, inv_inv]; simp
      rw [pow_comm]; rfl


theorem mul_pow (a b : G) (n : ℕ) : a * b = b * a -> pow (a * b) n = pow a n * pow b n := by
  intro H
  induction n with
  | zero => simp
  | succ n' IH =>
    simp
    rw [mul_assoc, IH, <- mul_assoc]
    have H' : b * a = a * b := by rw [H]
    rw [<- mul_assoc, mul_assoc a b, pow_comm b a n' H', <- mul_assoc, <- mul_assoc]

theorem comm_pow (a b : G) (n : ℕ) : a * b = b * a -> pow a n * pow b n = pow b n * pow a n := by
  intro H
  induction n with
  | zero => simp
  | succ n IH =>
    rw [pow_succ, pow_succ]
    rw [<- mul_assoc, mul_assoc _ _ b,  <-  pow_comm b a n, <- mul_assoc]
    rw [<- mul_assoc, mul_assoc b, <- pow_comm , <- mul_assoc, H]
    rw [mul_assoc, IH, <- mul_assoc]
    assumption
    rw [H]



theorem mul_Pow (a b : G) (n : ℤ) : a * b = b * a -> Pow (a * b) n = Pow a n * Pow b n := by
  intro H
  cases n with
  | ofNat n => rw [Pow_ofNat, Pow_ofNat, Pow_ofNat, mul_pow]; assumption
  | negSucc n =>
    have H' : b⁻¹ * a⁻¹ = a⁻¹ * b⁻¹ := by
      rw [<- mul_inv_rev, H, mul_inv_rev]
    rw [Pow_negSucc, Pow_negSucc, Pow_negSucc, mul_inv_rev, mul_pow ]
    rw [pow_succ, pow_succ]
    rw [<- mul_assoc, mul_assoc _ _ a⁻¹,  <-  pow_comm a⁻¹ b⁻¹ n, <- mul_assoc]
    rw [<- mul_assoc, mul_assoc a⁻¹, <- pow_comm , <- mul_assoc, H']
    rw [mul_assoc, comm_pow, <- mul_assoc]
    rw [H']; rw [H']; rw [H']; rw [H']






class Abelian (G) [Group G] : Prop where
  mul_comm : ∀ a b : G, a * b = b * a


end Group


section Permutation

open Equiv

instance {X : Type} : Group (Perm X) where
  mul f g := {
    toFun := f ∘ g
    invFun := g.invFun ∘ f.invFun
    left_inv := by intro x; simp
    right_inv := by intro x; simp
  }

  one := {
    toFun := id
    invFun := id
    left_inv := by intro x; simp
    right_inv := by intro x; simp
  }

  inv f := {
    toFun := f.invFun
    invFun := f.toFun
    left_inv := by intro x; simp
    right_inv := by intro x; simp
  }

  mul_assoc := by intro f g h; ext x; dsimp
  one_mul := by intro f; ext x; dsimp
  mul_inv_left := by intro f; ext x; simp

def PermGroup (X : Type) := Group (Perm X)


variable (X : Type)(σ τ : Perm X) (H K : PermGroup X)

end Permutation






end GroupTheory
