module cat where

-- Agda 2.6.0.1, stdLib v1.0
open import Library

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
iso : {A B : Obj} → (f : Mor A B) → (g : Mor B A) → Set
iso {A} {B} f g = (f ∘ g ≡ id {B}) × (g ∘ f ≡ id {A})

record _≅_ (A B : Obj) : Set where
  field
    f      : Mor A B
    g      : Mor B A
    f∘g≡id : f ∘ g ≡ id {B}
    g∘f≡id : g ∘ f ≡ id {A}

-- 1.5 Monics and Epics
-- Definition 1.5.1
monic : {A B : Obj} → (f : Mor A B) → Set
monic {A} {B} f = {T : Obj} → {g h : Mor T A} → f ∘ g ≡ f ∘ h → g ≡ h

-- Theorem 1.5.2
composite-monic : ∀ {A B C : Obj} {f : Mor A B} {g : Mor B C} → monic f → monic g → monic (g ∘ f)
composite-monic {f = f} {g} monic-f monic-g {g = h} {h = k} g∘f∘h≡g∘f∘k = monic-f (monic-g lemma)
  where
    lemma : g ∘ (f ∘ h) ≡ g ∘ (f ∘ k)
    lemma =
      begin
        g ∘ (f ∘ h)
      ≡⟨ sym ass ⟩
        (g ∘ f) ∘ h
      ≡⟨ g∘f∘h≡g∘f∘k ⟩
        (g ∘ f) ∘ k
      ≡⟨ ass ⟩
        g ∘ (f ∘ k)
      ∎

-- Definition 1.5.4
epic : {A B : Obj} → (f : Mor A B) → Set
epic {A} {B} f = {T : Obj} → {g h : Mor B T} → g ∘ f ≡ h ∘ f → g ≡ h

-- Exercise 1.5.5
composite-epic : ∀ {A B C : Obj} {f : Mor A B} {g : Mor B C} → epic f → epic g → epic (g ∘ f)
composite-epic {f = f} {g} epic-f epic-g {g = h} {h = k} h∘g∘f≡k∘g∘f = epic-g (epic-f lemma)
  where
    lemma : (h ∘ g) ∘ f ≡ (k ∘ g) ∘ f
    lemma =
      begin
        (h ∘ g) ∘ f
      ≡⟨ ass ⟩
        h ∘ (g ∘ f)
      ≡⟨ h∘g∘f≡k∘g∘f ⟩
        k ∘ (g ∘ f)
      ≡⟨ sym ass ⟩
        (k ∘ g) ∘ f
      ∎

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

-- Theorem 1.5.8
monic-split-epic→iso : {A B : Obj} {f : Mor A B} {g : Mor B A} →
                       monic f → split-epic f {g} → iso f g
monic-split-epic→iso {A} {B} {f} {g} monic-f f∘g≡id = f∘g≡id , monic-f lemma
  where
    lemma : f ∘ (g ∘ f) ≡ f ∘ id
    lemma =
      begin
        f ∘ (g ∘ f)
      ≡⟨ sym ass ⟩
        (f ∘ g) ∘ f
      ≡⟨ cong (_∘ f) f∘g≡id ⟩
        id ∘ f
      ≡⟨ idl ⟩
        f
      ≡⟨ sym idr ⟩
        f ∘ id
      ∎

iso→monic : {A B : Obj} {f : Mor A B} {g : Mor B A} → iso f g → monic f
iso→monic {A} {B} {f} {g} (f∘g≡id , g∘f≡id) {g = h} {h = k} f∘h≡f∘k =
  begin
    h
  ≡⟨ sym idl ⟩
    id ∘ h
  ≡⟨ sym (cong (_∘ h) g∘f≡id) ⟩
    (g ∘ f) ∘ h
  ≡⟨ ass ⟩
    g ∘ (f ∘ h)
  ≡⟨ cong (g ∘_) f∘h≡f∘k ⟩
    g ∘ (f ∘ k)
  ≡⟨ sym ass ⟩
    (g ∘ f) ∘ k
  ≡⟨ cong (_∘ k) g∘f≡id ⟩
    id ∘ k
  ≡⟨ idl ⟩
    k
  ∎

iso→split-epic : {A B : Obj} {f : Mor A B} {g : Mor B A} → iso f g → split-epic f {g}
iso→split-epic {A} {B} {f} {g} (f∘g≡id , g∘f≡id) = f∘g≡id
