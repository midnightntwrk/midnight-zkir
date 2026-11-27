{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerByteValues (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Operations ⋯
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯ using (StoreTyped; bind-success; writes-types)
open import zkir-v4.ProducerValuesHelpers ⋯

open import Data.Bool using (if_then_else_; _∧_)
open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_; _++_; take; drop; length; foldr; replicate)
  renaming (reverse to reverse-list)
import Data.List.Properties as LP
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
  renaming (map to map-maybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; suc; _+_; _≟_; _≤?_; _<?_; _≤_; _≤ᵇ_)
import Data.Nat.Properties as NP
open import Data.Product using (_×_; _,_; ∃)
open import Data.Vec using (Vec; toList)
open import Data.Vec.Properties using (length-toList)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (does)

private
  vector-width : ∀ {n} (vec : Vec Byte n) {bs k}
               → just (toList vec) ≡ just bs → just n ≡ just k → length bs ≡ k
  vector-width vec refl refl = length-toList vec

  sec1-width : ∀ {P : Set} (eq : DecidableEquality P) i f p
             → length (sec1-bytes eq i f p) ≡ 33
  sec1-width eq i f p with eq p i
  ... | yes _ = LP.length-replicate 33 {x = zero {255}}
  ... | no _ = length-toList (f p)

  repr-bytes : ∀ v {bs n} → to-bytes-value v ≡ just bs
             → repr-width (typeof v) ≡ just n → length bs ≡ n
  repr-bytes (val-native v) = vector-width (nativeToBytes v)
  repr-bytes (val-jubjub-scalar v) = vector-width (jubjubScalarToBytes v)
  repr-bytes (val-secp256k1-base v) = vector-width (secp256k1BaseToBytes v)
  repr-bytes (val-secp256k1-scalar v) = vector-width (secp256k1ScalarToBytes v)
  repr-bytes (val-secp256r1-base v) = vector-width (secp256r1BaseToBytes v)
  repr-bytes (val-secp256r1-scalar v) = vector-width (secp256r1ScalarToBytes v)
  repr-bytes (val-curve25519-base v) = vector-width (curve25519BaseToBytes v)
  repr-bytes (val-curve25519-scalar v) = vector-width (curve25519ScalarToBytes v)
  repr-bytes (val-jubjub-point v) = vector-width (jubjubPointToBytes v)
  repr-bytes (val-curve25519-point v) = vector-width (curve25519PointToBytes v)
  repr-bytes (val-secp256k1-point p) refl refl = sec1-width _≟K1_ idK1 secp256k1PointToBytes p
  repr-bytes (val-secp256r1-point p) refl refl = sec1-width _≟P_ idP secp256r1PointToBytes p
  repr-bytes (val-bytes _) ()
  repr-bytes (val-byte _) ()
  repr-bytes (val-bool _) ()
  repr-bytes (val-accumulator _) ()

  byte-resolution : ∀ sig Γ m x n → StoreTyped Γ m → bytelen sig Γ x ≡ just n
                  → ∃ λ bs → resolve-bytes m x ≡ just bs × length bs ≡ n
  byte-resolution sig Γ m x n store typed with bind-success (ty sig Γ x) width typed
  ... | t , found , sized with operand sig Γ m x store found
  ...   | value , resolved , value-type = select value resolved (subst (λ u → width u ≡ just n) (sym value-type) sized)
    where
    select : ∀ v → resolve m x ≡ just v → width (typeof v) ≡ just n
           → ∃ λ bs → resolve-bytes m x ≡ just bs × length bs ≡ n
    select (val-bytes bs) resolved len rewrite resolved = bs , refl , just-injective len
    select (val-native _) _ ()
    select (val-byte _) _ ()
    select (val-bool _) _ ()
    select (val-accumulator _) _ ()
    select (val-jubjub-point _) _ ()
    select (val-jubjub-scalar _) _ ()
    select (val-secp256k1-point _) _ ()
    select (val-secp256k1-base _) _ ()
    select (val-secp256k1-scalar _) _ ()
    select (val-secp256r1-point _) _ ()
    select (val-secp256r1-base _) _ ()
    select (val-secp256r1-scalar _) _ ()
    select (val-curve25519-point _) _ ()
    select (val-curve25519-base _) _ ()
    select (val-curve25519-scalar _) _ ()

  mapped-type : ∀ {A : Set} t (mk : A → IrValue) → (∀ a → typeof (mk a) ≡ t)
              → ∀ p {v} → map-maybe mk p ≡ just v → typeof v ≡ t
  mapped-type t mk typed nothing ()
  mapped-type t mk typed (just a) refl = typed a

  point-type : ∀ {A : Set} t (mk : A → IrValue) → (∀ a → typeof (mk a) ≡ t)
             → ∀ n (encode-point : A → Vec Byte n) (decode-point : Vec Byte n → Maybe A) bs {v}
             → (as-vector n bs >>= λ raw → decode-point raw >>= λ point →
               guardD (bs ≟B toList (encode-point point)) (just (mk point))) ≡ just v
             → typeof v ≡ t
  point-type t mk typed n encode-point decode-point bs ok
    with bind-success (as-vector n bs) _ ok
  ... | raw , _ , decoded with bind-success (decode-point raw) _ decoded
  ...   | pt , _ , canonical with checked (bs ≟B toList (encode-point pt)) {r = just (mk pt)} canonical
  ...     | _ , kept = trans (cong typeof (sym (just-injective kept))) (typed pt)

  decoded-type : ∀ t bs {v} → from-bytes-value t bs ≡ just v → typeof v ≡ t
  decoded-type native _ refl = refl
  decoded-type jubjub-scalar _ refl = refl
  decoded-type secp256k1-base _ refl = refl
  decoded-type secp256k1-scalar _ refl = refl
  decoded-type secp256r1-base _ refl = refl
  decoded-type secp256r1-scalar _ refl = refl
  decoded-type curve25519-base _ refl = refl
  decoded-type curve25519-scalar _ refl = refl
  decoded-type jubjub-point bs =
    point-type jubjub-point val-jubjub-point (λ _ → refl) 32 jubjubPointToBytes jubjubPointFromBytes bs
  decoded-type curve25519-point bs =
    point-type curve25519-point val-curve25519-point (λ _ → refl) 32 curve25519PointToBytes curve25519PointFromBytes bs
  decoded-type secp256k1-point bs =
    mapped-type secp256k1-point val-secp256k1-point (λ _ → refl)
      (sec1-point _≟K1_ idK1 secp256k1PointToBytes secp256k1PointFromBytes bs)
  decoded-type secp256r1-point bs =
    mapped-type secp256r1-point val-secp256r1-point (λ _ → refl)
      (sec1-point _≟P_ idP secp256r1PointToBytes secp256r1PointFromBytes bs)
  decoded-type (bytes _) _ ()
  decoded-type byte _ ()
  decoded-type bool _ ()
  decoded-type accumulator _ ()

  from-result : ∀ t b o {ws} → (from-bytes-value t b >>= write o) ≡ just ws
              → writes-types ws ≡ (o ⦂ t) ∷ []
  from-result t b o ok with bind-success (from-bytes-value t b) (write o) ok
  ... | v , decoded , written = write-type o v (decoded-type t b decoded) written

into32-types : ∀ sig Γ m → StoreTyped Γ m → ∀ x o → Rule sig Γ m (into-bytes32 x o)
into32-types sig Γ m _ x o inferred ok
  with bind-success (resolve m x >>= to-bytes-value) _ ok
     | bind-success (ty sig Γ x >>= repr-width) _ inferred
... | bs , _ , guarded | n , _ , out with checked (length bs ≟ 32) guarded
...   | size , applied =
  fixed (write-type o (val-bytes bs) (cong bytes size) applied)
    (skip (demand (does (n ≟ 32))) out)

from32-types : ∀ sig Γ m → StoreTyped Γ m → ∀ x t o → Rule sig Γ m (from-bytes32 x t o)
from32-types sig Γ m _ x t o inferred ok
  with bind-success (resolve-bytes m x) _ ok
... | bs , _ , guarded with checked (length bs ≟ 32) guarded
...   | _ , decoded = fixed (from-result t bs o decoded)
  (skip (expect sig Γ bytes32 x >> demand (from-width 32 t)) inferred)

from-bytes-types : ∀ sig Γ m → StoreTyped Γ m → ∀ x t o → Rule sig Γ m (from-bytes x t o)
from-bytes-types sig Γ m _ x t o inferred ok
  with bind-success (bytelen sig Γ x) _ inferred
     | bind-success (resolve-bytes m x >>= from-bytes-value t) _ ok
... | n , _ , result | v , parsed , written
  with bind-success (resolve-bytes m x) (from-bytes-value t) parsed
...   | raw , _ , decoded =
  fixed (write-type o v (decoded-type t raw decoded) written)
    (skip (demand (from-width n t)) result)

to-bytes-types : ∀ sig Γ m → StoreTyped Γ m → ∀ x o → Rule sig Γ m (to-bytes x o)
to-bytes-types sig Γ m store x o inferred ok
  with bind-success (ty sig Γ x >>= repr-width) _ inferred
     | bind-success (resolve m x >>= to-bytes-value) _ ok
... | n , sized , out | bs , encoded , used
  with bind-success (ty sig Γ x) repr-width sized
     | bind-success (resolve m x) to-bytes-value encoded
...   | t , src-type , size | v , seen , produced with operand sig Γ m x store src-type
...     | actual , resolved , typed with just-injective (trans (sym seen) resolved)
...       | refl =
  fixed (write-type o (val-bytes bs)
    (cong bytes (repr-bytes v produced (subst (λ u → repr-width u ≡ just n) (sym typed) size))) used) out

reverse-types : ∀ sig Γ m → StoreTyped Γ m → ∀ x o → Rule sig Γ m (reverse x o)
reverse-types sig Γ m store x o inferred ok
  with bind-success (bytelen sig Γ x) _ inferred
... | n , sized , out with byte-resolution sig Γ m x n store sized
...   | bs , seen , len rewrite seen =
  fixed (write-type o (val-bytes (reverse-list bs)) (cong bytes (trans (LP.length-reverse bs) len)) ok) out

reverse32-types : ∀ sig Γ m → StoreTyped Γ m → ∀ x o → Rule sig Γ m (reverse-bytes x o)
reverse32-types = reverse-types

slice-types : ∀ sig Γ m → StoreTyped Γ m → ∀ x start n o → Rule sig Γ m (slice x start n o)
slice-types sig Γ m _ x start n o inferred ok
  with bind-success (bytelen sig Γ x) _ inferred
     | bind-success (resolve-bytes m x) _ ok
... | w , _ , out | bs , _ , guarded
  with checked (0 <? n) guarded
... | _ , within with checked (start + n ≤? length bs) within
...   | fits , applied =
  fixed (write-type o (val-bytes (take n (drop start bs))) (cong bytes len) applied)
    (skip (demand (valid-bytes-length n ∧ ((start + n) ≤ᵇ w))) out)
  where
  len : length (take n (drop start bs)) ≡ n
  len rewrite LP.length-take n (drop start bs) | LP.length-drop start bs =
    NP.m≤n⇒m⊓n≡m (NP.m+n≤o⇒m≤o∸n n (subst (_≤ length bs) (NP.+-comm start n) fits))

parts-length : ∀ l h {bs} → bytes32-from-parts l h ≡ just bs → length bs ≡ 32
parts-length l h ok
  with bind-success (to-bytes-value l) _ ok
... | lo , _ , high with bind-success (to-bytes-value h) _ high
...   | hi , _ , bounds with checked (length lo ≟ 32) bounds
...     | low-width , hi-check with checked (length hi ≟ 32) hi-check
...       | high-width , low-zero with checked (drop 31 lo ≟B (zero ∷ [])) low-zero
...         | _ , high-zero with checked (drop 1 hi ≟B replicate 31 zero) high-zero
...           | _ , refl
  rewrite LP.length-++ (take 31 lo) {ys = take 1 hi}
        | LP.length-take 31 lo | LP.length-take 1 hi | low-width | high-width = refl

parts-types : ∀ sig Γ m → StoreTyped Γ m → ∀ xy o → Rule sig Γ m (bytes32-from-low-high xy o)
parts-types sig Γ m _ (l , h) o inferred ok
  with bind-success (resolve m l) _ ok
... | lo , _ , high with bind-success (resolve m h) _ high
...   | hi , _ , parts with bind-success (bytes32-from-parts lo hi) _ parts
...     | bs , formed , used =
  fixed (write-type o (val-bytes bs) (cong bytes (parts-length lo hi formed)) used)
    (skip (expect sig Γ native l >> expect sig Γ native h) inferred)

private
  concat-step : ∀ m x xs v n rest k → resolve m x ≡ just v → concat-width (typeof v) ≡ just n
              → resolve-concat m xs ≡ just rest → length rest ≡ k
              → ∃ λ bs → resolve-concat m (x ∷ xs) ≡ just bs × length bs ≡ n + k
  concat-step m x xs (val-byte b) n rest k seen refl tail len rewrite seen | tail =
    (b ∷ rest) , refl , cong suc len
  concat-step m x xs (val-bytes bs) n rest k seen refl tail len rewrite seen | tail =
    (bs ++ rest) , refl , trans (LP.length-++ bs) (cong (length bs +_) len)
  concat-step m x xs (val-native _) _ _ _ _ ()
  concat-step m x xs (val-bool _) _ _ _ _ ()
  concat-step m x xs (val-accumulator _) _ _ _ _ ()
  concat-step m x xs (val-jubjub-point _) _ _ _ _ ()
  concat-step m x xs (val-jubjub-scalar _) _ _ _ _ ()
  concat-step m x xs (val-secp256k1-point _) _ _ _ _ ()
  concat-step m x xs (val-secp256k1-base _) _ _ _ _ ()
  concat-step m x xs (val-secp256k1-scalar _) _ _ _ _ ()
  concat-step m x xs (val-secp256r1-point _) _ _ _ _ ()
  concat-step m x xs (val-secp256r1-base _) _ _ _ _ ()
  concat-step m x xs (val-secp256r1-scalar _) _ _ _ _ ()
  concat-step m x xs (val-curve25519-point _) _ _ _ _ ()
  concat-step m x xs (val-curve25519-base _) _ _ _ _ ()
  concat-step m x xs (val-curve25519-scalar _) _ _ _ _ ()

  concat-resolution : ∀ sig Γ m xs ns → StoreTyped Γ m
                    → check-list (λ x → ty sig Γ x >>= concat-width) xs ≡ just ns
                    → ∃ λ bs → resolve-concat m xs ≡ just bs × length bs ≡ foldr _+_ 0 ns
  concat-resolution sig Γ m [] .[] _ refl = [] , refl , refl
  concat-resolution sig Γ m (x ∷ xs) ns store typed
    with bind-success (ty sig Γ x >>= concat-width) _ typed
  ... | n , inferred , code
    with bind-success (ty sig Γ x) concat-width inferred
       | bind-success (check-list (λ op → ty sig Γ op >>= concat-width) xs) _ code
  ...   | t , head-type , sized | ks , tail-code , refl
    with operand sig Γ m x store head-type | concat-resolution sig Γ m xs ks store tail-code
  ...     | v , seen , refl | tail , resolved , len =
    concat-step m x xs v n tail (foldr _+_ 0 ks) seen sized resolved len

concat-types : ∀ sig Γ m → StoreTyped Γ m → ∀ xs o → Rule sig Γ m (concat xs o)
concat-types sig Γ m store xs o inferred ok
  with bind-success (check-list (λ op → ty sig Γ op >>= concat-width) xs) _ inferred
... | ns , widths , out with concat-resolution sig Γ m xs ns store widths
...   | bs , resolved , len rewrite resolved =
  fixed (write-type o (val-bytes bs) (cong bytes len)
        (take-result (valid-bytes-length (length bs)) ok))
        (skip (demand (valid-bytes-length (foldr _+_ 0 ns))) out)
