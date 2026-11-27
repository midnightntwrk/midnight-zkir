{-# OPTIONS --safe #-}
module zkir-v4.ProofSlots where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base as M using (Maybe; just; nothing)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

-- The guard list is the sequence evaluated at InnerProof instructions.
-- A slot is mandatory for each instruction.  A false guard erases its
-- contents before the VM records its witness.
module _ {A : Set} where

  keep : Bool → List A → List A
  keep true  bs = bs
  keep false bs = []

  normalize : List Bool → List (List A) → Maybe (List (List A))
  normalize []       []       = just []
  normalize []       (_ ∷ _)  = nothing
  normalize (_ ∷ _)  []       = nothing
  normalize (g ∷ gs) (b ∷ bs) = M.map (keep g b ∷_) (normalize gs bs)

  data Canonical : List Bool → List (List A) → Set where
    end : Canonical [] []
    active : ∀ {gs bs b} → Canonical gs bs → Canonical (true ∷ gs) (b ∷ bs)
    inactive : ∀ {gs bs} → Canonical gs bs → Canonical (false ∷ gs) ([] ∷ bs)

  normalized-canonical : ∀ gs bs {xs} → normalize gs bs ≡ just xs → Canonical gs xs
  normalized-canonical [] [] refl = end
  normalized-canonical (true ∷ gs) (b ∷ bs) eq with normalize gs bs in h
  ... | just xs with eq
  ...   | refl = active (normalized-canonical gs bs h)
  normalized-canonical (false ∷ gs) (b ∷ bs) eq with normalize gs bs in h
  ... | just xs with eq
  ...   | refl = inactive (normalized-canonical gs bs h)

  canonical-fixed : ∀ {gs bs} → Canonical gs bs → normalize gs bs ≡ just bs
  canonical-fixed end = refl
  canonical-fixed (active c) rewrite canonical-fixed c = refl
  canonical-fixed (inactive c) rewrite canonical-fixed c = refl

  canonical-unique : ∀ {gs bs cs}
                   → Canonical gs bs → Canonical gs cs
                   → normalize gs bs ≡ normalize gs cs → bs ≡ cs
  canonical-unique cb cc eq with trans (sym (canonical-fixed cb)) (trans eq (canonical-fixed cc))
  ... | refl = refl
