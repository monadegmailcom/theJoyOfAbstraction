import Mathlib.CategoryTheory.Category.Basic

open CategoryTheory

inductive Obj where
  | a : Obj
  | b : Obj
  | c : Obj
  | d : Obj

inductive Mor : Obj -> Obj -> Type where
  | idx x : Mor x x
  | fab : Mor Obj.a Obj.b
  | fbc : Mor Obj.b Obj.c
  | fac : Mor Obj.a Obj.c
  | fcd : Mor Obj.c Obj.d
  | fbd : Mor Obj.b Obj.d
  | fad : Mor Obj.a Obj.d

-- a -> b -> c -> d
instance : Category Obj where
  Hom := fun x y => Mor x y
  id (x : Obj) := Mor.idx x
  comp f g := match f, g with
    | Mor.idx _, g => g
    | f, Mor.idx _ => f
    | Mor.fac, Mor.fcd => Mor.fad
    | Mor.fbc, Mor.fcd => Mor.fbd
    | Mor.fab, Mor.fbd => Mor.fad
    | Mor.fab, Mor.fbc => Mor.fac
  comp_id f := by match f with
    | Mor.idx _ => rfl
    | Mor.fab => rfl
    | Mor.fbc => rfl
    | Mor.fac => rfl
    | Mor.fcd => rfl
    | Mor.fbd => rfl
    | Mor.fad => rfl
  id_comp f := by match f with
    | Mor.idx _ => rfl
    | Mor.fab => rfl
    | Mor.fbc => rfl
    | Mor.fac => rfl
    | Mor.fcd => rfl
    | Mor.fbd => rfl
    | Mor.fad => rfl
  assoc f g h := by match f, g, h with
    | Mor.idx _, _, _ => simp
    | Mor.fab, Mor.idx _, Mor.idx _ => simp
    | Mor.fab, Mor.idx _, Mor.fbc => simp
    | Mor.fab, Mor.idx _, Mor.fbd => simp
    | Mor.fab, Mor.fbc, Mor.idx _ => simp
    | Mor.fab, Mor.fbc, Mor.fcd => simp
    | Mor.fab, Mor.fbd, Mor.idx _ => simp
    | Mor.fac, Mor.idx _, Mor.idx _ => simp
    | Mor.fac, Mor.idx _, Mor.fcd => simp
    | Mor.fac, Mor.fcd, Mor.idx _ => simp
    | Mor.fad, Mor.idx _, Mor.idx _ => simp
    | Mor.fbc, Mor.idx _, Mor.idx _ => simp
    | Mor.fbc, Mor.fcd, Mor.idx _ => simp
    | Mor.fbc, Mor.idx _, Mor.fcd => simp
    | Mor.fbd, Mor.idx _, Mor.idx _ => simp
    | Mor.fcd, Mor.idx _, Mor.idx _ => simp
