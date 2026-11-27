{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerValuesHelpers (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Operations ⋯
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯ using (StoreTyped; typed-operand; writes-types; bind-success)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (_≟_)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)

-- Eliminate fallible prefixes on either side while retaining the
-- successful value for the operations whose result type depends on it.
skip : ∀ {A B : Set} (x : Maybe A) {r : Maybe B} {v} → (x >> r) ≡ just v → r ≡ just v
skip nothing ()
skip (just _) ok = ok

mapped-bind-success : ∀ {A B C : Set} (m : Maybe A) (map-value : A → B) (f : B → Maybe C) {v}
  → ((m >>= λ a → just (map-value a)) >>= f) ≡ just v
  → ∃ λ a → (m ≡ just a) × (f (map-value a) ≡ just v)
mapped-bind-success nothing _ _ ()
mapped-bind-success (just a) _ _ ok = a , refl , ok

checked : ∀ {A P : Set} (d : Dec P) {r : Maybe A} {v} → guardD d r ≡ just v → P × r ≡ just v
checked (no _) ()
checked (yes p) ok = p , ok

take-result : ∀ {A : Set} {v : A} (g : Bool) {x} → (if g then x else nothing) ≡ just v → x ≡ just v
take-result true ok = ok
take-result false ()

fixed : ∀ {a bs actual : Env} → a ≡ actual → just actual ≡ just bs → a ≡ bs
fixed ty-ok eq = trans ty-ok (just-injective eq)

write-type : ∀ id v {ws t} → typeof v ≡ t → write id v ≡ just ws → writes-types ws ≡ (id ⦂ t) ∷ []
write-type id v refl refl = refl

native-writes : ∀ os vs {ws} → writes os (map val-native vs) ≡ just ws
              → writes-types ws ≡ map (_⦂ native) os
native-writes [] [] refl = refl
native-writes (_ ∷ _) [] ()
native-writes [] (_ ∷ _) ()
native-writes (o ∷ os) (x ∷ vs) ok with bind-success (writes os (map val-native vs)) _ ok
... | rest , tail-ok , end with refl ← just-injective end =
  cong ((o ⦂ native) ∷_) (native-writes os vs tail-ok)

inferred-natives : ∀ sig Γ n os {bs} → natives sig Γ n os ≡ just bs → just (map (_⦂ native) os) ≡ just bs
inferred-natives sig Γ n os = skip (demand (does (length os ≟ n)))

equality : ∀ {t u} → demand (equal t u) ≡ just tt → t ≡ u
equality {t} {u} ok with t ≟T u
... | yes eq = eq
... | no _ with () ← ok

operand : ∀ sig Γ m op {t} → StoreTyped Γ m → ty sig Γ op ≡ just t →
          ∃ λ v → resolve m op ≡ just v × typeof v ≡ t
operand sig Γ m op = typed-operand {signature = sig} {Γ} {m} {op}

unary-output : ∀ sig Γ m pred x o {bs} → StoreTyped Γ m → unary sig Γ pred x o ≡ just bs
  → ∃ λ v → resolve m x ≡ just v × ((o ⦂ typeof v) ∷ [] ≡ bs)
unary-output sig Γ m pred x o store ok with bind-success (ty sig Γ x) _ ok
... | t , found , step with operand sig Γ m x store found
...   | v , seen , refl = v , seen , just-injective (skip (demand (pred (typeof v))) step)

binary-output : ∀ sig Γ m pred a b o {bs} → StoreTyped Γ m → binary sig Γ pred a b o ≡ just bs
  → ∃ λ x → ∃ λ y → resolve m a ≡ just x × resolve m b ≡ just y × typeof y ≡ typeof x × ((o ⦂ typeof x) ∷ [] ≡ bs)
binary-output sig Γ m pred a b o store ok with bind-success (ty sig Γ a) _ ok
... | t , fa , checks with bind-success (expect sig Γ t b >> demand (pred t)) _ checks
...   | tt , both , final with bind-success (expect sig Γ t b) _ both
...     | tt , passed , _ with bind-success (ty sig Γ b) _ passed
...       | u , fb , equal-types with operand sig Γ m a store fa | operand sig Γ m b store fb
...         | x , ra , refl | y , rb , refl =
  x , y , ra , rb , sym (equality equal-types) , just-injective final

expect-operand : ∀ sig Γ m op t → StoreTyped Γ m → expect sig Γ t op ≡ just tt
  → ∃ λ v → resolve m op ≡ just v × typeof v ≡ t
expect-operand sig Γ m op t typed ok with bind-success (ty sig Γ op) _ ok
... | u , found , eq with operand sig Γ m op typed found
...   | v , ra , vu = v , ra , trans vu (sym (equality eq))

Rule : List IrType → Env → Mem → Instruction → Set
Rule sig Γ m i = ∀ {bs ws} → bindings sig Γ i ≡ just bs → compute m i ≡ just ws → writes-types ws ≡ bs
