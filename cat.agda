module cat where

-- Agda 2.6.0.1, stdLib v1.0
open import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

postulate
  Obj : Set
  Mor : Obj → Obj → Set
  id  : ∀{A} → Mor A A
  _∘_ : ∀{A B C} → Mor B C → Mor A B → Mor A C
  idl : ∀{A B} {f : Mor A B} → id ∘ f ≡ f
  idr : ∀{A B} {f : Mor A B} → f ∘ id ≡ f
  ass : ∀{A B C D} {f : Mor B C} {g : Mor A B} {h : Mor D A} →
        (f ∘ g) ∘ h ≡ f ∘ (g ∘ h)

-- 1.4 Isomorphisms
-- Definition 1.4.1 Left and Right Inverses
-- g is a right inverse to f
-- f is a left inverse to g
inv : {A B : Obj} → (f : Mor A B) → (g : Mor B A) → Set
inv {A} {B} f g = f ∘ g ≡ id {B}

-- Definition 1.4.2 Isomorphism
iso-mor : {A B : Obj} → (f : Mor A B) → (g : Mor B A) → Set
iso-mor f g = f ∘ g ≡ id → g ∘ f ≡ id

iso-obj : (A B : Obj) → {f : Mor A B} → {g : Mor B A} → Set
iso-obj A B {f} {g} = iso-mor f g

-- 1.5 Monics and Epics
-- Definition 1.5.1
monic : {A B : Obj} → (f : Mor A B) → Set
monic {A} {B} f = {T : Obj} → {g h : Mor T A} → f ∘ g ≡ f ∘ h → g ≡ h

-- Definition 1.5.4
epic : {A B : Obj} → (f : Mor A B) → Set
epic {A} {B} f = {T : Obj} → {g h : Mor B T} → g ∘ f ≡ h ∘ f → g ≡ h

-- Definition 1.5.6
split-epic : {A B : Obj} → (f : Mor A B) → {g : Mor B A} → Set
split-epic {A} {B} f {g} = inv f g

-- Theorem 1.5.7
split-epit→epic : {A B : Obj} {f : Mor A B} {g : Mor B A} → split-epic f {g} → epic f
split-epit→epic {f = f} {g} f∘g≡id {g = h} {h = k} h∘f≡k∘f =
  begin
    h
  ≡⟨ sym idr ⟩
    (h ∘ id)
  ≡⟨ cong (h ∘_) (sym f∘g≡id) ⟩
    (h ∘ (f ∘ g))
  ≡⟨ sym ass ⟩
    ((h ∘ f) ∘ g)
  ≡⟨ cong (_∘ g) h∘f≡k∘f ⟩
    ((k ∘ f) ∘ g)
  ≡⟨ ass ⟩
    (k ∘ (f ∘ g))
  ≡⟨ cong (k ∘_) f∘g≡id ⟩
    (k ∘ id)
  ≡⟨ idr ⟩
    k
  ∎
