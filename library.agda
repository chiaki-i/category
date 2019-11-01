module Library where

open import Relation.Binary.PropositionalEquality as Eq

open Eq
  using (_≡_; refl; cong; sym) public

open Eq.≡-Reasoning
  using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎) public

open import Data.Product
  using (_,_; _×_) public
