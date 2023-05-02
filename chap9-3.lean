import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

def divides (x y : Nat) : Prop := ∃ k, k * x = y

theorem divides_trans (h1 : divides x y) (h2 : divides y z)
      : divides x z :=
  let ⟨k1, d1⟩ := h1
  let ⟨k2, d2⟩ := h2
  let proof : (k1 * k2) * x = z := calc
    (k1 * k2) * x = (k2 * k1) * x := by rw [Nat.mul_comm k1 k2]
    _ = k2 * (k1 * x) := by rw [Nat.mul_assoc]
    _ = k2 * y := by rw [d1]
    _ = z := d2
  ⟨k1 * k2, proof⟩

theorem n_div_n {n : Nat} : divides n n := ⟨1, by simp⟩

namespace Finit

structure Obj (n : Nat) where
  val : Nat
  isDiv : divides val n

inductive Mor : Obj n -> Obj n -> Type where
  | mk i j : divides i.val j.val -> Mor i j

instance : Category (Obj n) where
  Hom x y := Mor x y
  id x := Mor.mk x x n_div_n
  comp f g := match f, g with
    | Mor.mk _ _ h1, Mor.mk _ _ h2
      => Mor.mk _ _ (divides_trans h1 h2)

-- samples
def o5 : Obj 30 := Obj.mk 5 ⟨6, by simp⟩
def o15 : Obj 30 := Obj.mk 15 ⟨2, by simp⟩
def f315 : Mor o5 o15 := Mor.mk o5 o15 ⟨3, by simp⟩

example {n : Nat} : divides 1 n := ⟨n, by simp⟩

end Finit

namespace Infinit

inductive Mor : Nat -> Nat -> Type where
  | mk i j : divides i j -> Mor i j

instance : Category Nat where
  Hom x y := Mor x y
  id x := Mor.mk x x n_div_n
  comp f g := match f, g with
    | Mor.mk _ _ h1, Mor.mk _ _ h2
      => Mor.mk _ _ (divides_trans h1 h2)

-- samples
def f315 : Mor 3 15 := Mor.mk 3 15 ⟨5, by simp⟩

end Infinit
