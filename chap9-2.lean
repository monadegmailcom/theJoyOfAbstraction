import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

-- x -> y <=> x ~ y <=> r x y
inductive Mor : (a -> a -> Prop) -> a -> a -> Type where
  | mk x y : r x y -> Mor r x y

set_option synthInstance.checkSynthOrder false
instance [IsRefl a r] [IsTrans a r] : Category a where
  Hom x y := Mor r x y
  id x := Mor.mk x x (refl x)
  comp f g := match f, g with
    | Mor.mk _ _ r1, Mor.mk _ _ r2 => Mor.mk _ _ (_root_.trans r1 r2)

--samples
def n : Int := 6
def mod_n (i j : Int) : Prop := ∃ k, k * n = i - j
def refl_mod_n (i : Int) : mod_n i i :=
  let proof : 0 * n = (i-i) := calc
    0 * n = 0 := by simp
    _ = i - i := by rw [Int.sub_self]
  ⟨0, proof⟩
def symm_mod_n (h : mod_n i j) : mod_n j i :=
  let ⟨k, d⟩ := h
  let proof : (-k) * n = j - i := calc
    (-k) * n = -(k * n) := by rw [Int.neg_mul]
    _ = -(i - j) := by rw [d]
    _ = j - i := by rw [Int.neg_sub]
  ⟨-k, proof⟩
def trans_mod_n (h1: mod_n i j) (h2: mod_n j k) : mod_n i k :=
  let ⟨k1, d1⟩ := h1
  let ⟨k2, d2⟩ := h2
  let proof : (k1 + k2) * n = i - k := calc
    (k1 + k2) * n = k1 * n + k2 * n := by rw[Int.add_mul]
    _ = (i-j) + (j-k) := by rw[d1, d2]
    _ = (i + (-j)) + (j + (-k)) := by simp[Int.sub_eq_add_neg]
    _ = i + ((-j) + j) + (-k) := by simp[Int.add_assoc]
    _ = i + (j - j) + (-k) := by simp[Int.add_comm j, Int.sub_eq_add_neg, Int.sub_self]
    _ = i + (-k) := by rw[Int.sub_self, Int.add_zero]
  ⟨k1 + k2, proof⟩

instance : IsRefl Int mod_n where
  refl := refl_mod_n

instance : IsTrans Int mod_n where
  trans := fun _ _ _ => trans_mod_n

def f11 : (1 : Int) ⟶ 1 := 𝟙 1
def f17 : (1 : Int) ⟶ 7 := Mor.mk 1 7 ⟨-1, by simp⟩
def f713 : (7 : Int) ⟶ 13 := Mor.mk 7 13 ⟨-1, by simp⟩
def f113 : (1 : Int) ⟶ 13 := f17 ≫ f713
