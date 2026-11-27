{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerCurveValues (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Operations ⋯
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯ using (StoreTyped; bind-success; writes-types)
open import zkir-v4.ProducerValuesHelpers ⋯ using (Rule; fixed; write-type; operand; expect-operand; mapped-bind-success)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

private
  data ScalarFor : IrType → IrValue → Set where
    jubjub : ∀ v → ScalarFor jubjub-point (val-jubjub-scalar v)
    secp256k1 : ∀ v → ScalarFor secp256k1-point (val-secp256k1-scalar v)
    secp256r1 : ∀ v → ScalarFor secp256r1-point (val-secp256r1-scalar v)
    curve25519 : ∀ v → ScalarFor curve25519-point (val-curve25519-scalar v)

  scalar-for : ∀ v {t} → from-scalar (typeof v) ≡ just t → ScalarFor t v
  scalar-for (val-jubjub-scalar v) refl = jubjub v
  scalar-for (val-secp256k1-scalar v) refl = secp256k1 v
  scalar-for (val-secp256r1-scalar v) refl = secp256r1 v
  scalar-for (val-curve25519-scalar v) refl = curve25519 v
  scalar-for (val-native _) ()
  scalar-for (val-bytes _) ()
  scalar-for (val-byte _) ()
  scalar-for (val-bool _) ()
  scalar-for (val-accumulator _) ()
  scalar-for (val-jubjub-point _) ()
  scalar-for (val-secp256k1-point _) ()
  scalar-for (val-secp256k1-base _) ()
  scalar-for (val-secp256r1-point _) ()
  scalar-for (val-secp256r1-base _) ()
  scalar-for (val-curve25519-point _) ()
  scalar-for (val-curve25519-base _) ()

  curve-scalar : ∀ v {scalar base} → curve (typeof v) ≡ just (scalar , base)
               → from-scalar scalar ≡ just (typeof v)
  curve-scalar (val-native _) ()
  curve-scalar (val-bytes _) ()
  curve-scalar (val-byte _) ()
  curve-scalar (val-bool _) ()
  curve-scalar (val-accumulator _) ()
  curve-scalar (val-jubjub-point _) refl = refl
  curve-scalar (val-jubjub-scalar _) ()
  curve-scalar (val-secp256k1-point _) refl = refl
  curve-scalar (val-secp256k1-base _) ()
  curve-scalar (val-secp256k1-scalar _) ()
  curve-scalar (val-secp256r1-point _) refl = refl
  curve-scalar (val-secp256r1-base _) ()
  curve-scalar (val-secp256r1-scalar _) ()
  curve-scalar (val-curve25519-point _) refl = refl
  curve-scalar (val-curve25519-base _) ()
  curve-scalar (val-curve25519-scalar _) ()

  ec-mul-result : ∀ sig Γ m a b o p v {bs ws}
    → ScalarFor (typeof p) v
    → resolve m a ≡ just p → resolve m b ≡ just v
    → one sig Γ o (typeof p) ≡ just bs
    → compute m (ec-mul a b o) ≡ just ws
    → writes-types ws ≡ bs
  ec-mul-result sig Γ m a b o (val-jubjub-point p) _ (jubjub v) ra rb built run
    rewrite ra | rb = fixed (write-type o (val-jubjub-point (v ·J p)) refl run) built
  ec-mul-result sig Γ m a b o (val-secp256k1-point p) _ (secp256k1 v) ra rb built run
    rewrite ra | rb = fixed (write-type o (val-secp256k1-point (v ·K1 p)) refl run) built
  ec-mul-result sig Γ m a b o (val-secp256r1-point p) _ (secp256r1 v) ra rb built run
    rewrite ra | rb = fixed (write-type o (val-secp256r1-point (v ·P p)) refl run) built
  ec-mul-result sig Γ m a b o (val-curve25519-point p) _ (curve25519 v) ra rb built run
    rewrite ra | rb = fixed (write-type o (val-curve25519-point (v ·C p)) refl run) built
  ec-mul-result sig Γ m a b o (val-native _) _ ()
  ec-mul-result sig Γ m a b o (val-bytes _) _ ()
  ec-mul-result sig Γ m a b o (val-byte _) _ ()
  ec-mul-result sig Γ m a b o (val-bool _) _ ()
  ec-mul-result sig Γ m a b o (val-accumulator _) _ ()
  ec-mul-result sig Γ m a b o (val-jubjub-scalar _) _ ()
  ec-mul-result sig Γ m a b o (val-secp256k1-base _) _ ()
  ec-mul-result sig Γ m a b o (val-secp256k1-scalar _) _ ()
  ec-mul-result sig Γ m a b o (val-secp256r1-base _) _ ()
  ec-mul-result sig Γ m a b o (val-secp256r1-scalar _) _ ()
  ec-mul-result sig Γ m a b o (val-curve25519-base _) _ ()
  ec-mul-result sig Γ m a b o (val-curve25519-scalar _) _ ()

  generator-result : ∀ sig Γ m a o t v {bs ws}
    → ScalarFor t v → resolve m a ≡ just v → one sig Γ o t ≡ just bs
    → compute m (ec-mul-generator a o) ≡ just ws
    → writes-types ws ≡ bs
  generator-result sig Γ m a o _ _ (jubjub v) resolved built run
    rewrite resolved = fixed (write-type o (val-jubjub-point (v ·J genJ)) refl run) built
  generator-result sig Γ m a o _ _ (secp256k1 v) resolved built run
    rewrite resolved = fixed (write-type o (val-secp256k1-point (v ·K1 genK1)) refl run) built
  generator-result sig Γ m a o _ _ (secp256r1 v) resolved built run
    rewrite resolved = fixed (write-type o (val-secp256r1-point (v ·P genP)) refl run) built
  generator-result sig Γ m a o _ _ (curve25519 v) resolved built run
    rewrite resolved = fixed (write-type o (val-curve25519-point (v ·C genC)) refl run) built

ec-mul-types : ∀ sig Γ m a b o → StoreTyped Γ m → Rule sig Γ m (ec-mul a b o)
ec-mul-types sig Γ m a b o typed checked run
  with bind-success (ty sig Γ a) _ checked
... | t , t-point , get-curve
  with operand sig Γ m a typed t-point
... | p , rp , refl
  with bind-success (curve (typeof p)) _ get-curve
... | (scalar , base) , known-curve , scalar-check
  with bind-success (expect sig Γ scalar b) _ scalar-check
... | tt , t-scalar , built
  with expect-operand sig Γ m b scalar typed t-scalar
... | v , rv , refl =
  ec-mul-result sig Γ m a b o p v (scalar-for v (curve-scalar p known-curve)) rp rv built run

ec-mul-generator-types : ∀ sig Γ m a o → StoreTyped Γ m → Rule sig Γ m (ec-mul-generator a o)
ec-mul-generator-types sig Γ m a o typed checked run
  with bind-success (ty sig Γ a >>= from-scalar) (one sig Γ o) checked
... | t , inferred , built with bind-success (ty sig Γ a) from-scalar inferred
... | scalar , t-scalar , point with operand sig Γ m a typed t-scalar
... | v , resolved , refl =
  generator-result sig Γ m a o t v (scalar-for v point) resolved built run

module _ (sig : List IrType) (Γ : Env) (m : Mem) (store : StoreTyped Γ m) where
  private
    write-types-eq : ∀ {ws ws′ : List (Identifier × IrValue)} → just ws ≡ just ws′ → writes-types ws′ ≡ writes-types ws
    write-types-eq eq = cong writes-types (sym (just-injective eq))

    into-result : ∀ p x y v {bs ws}
      → resolve m p ≡ just v
      → (curve (typeof v) >>= λ { (_ , t) → just ((x ⦂ t) ∷ (y ⦂ t) ∷ []) }) ≡ just bs
      → compute m (into-coordinates p (x , y)) ≡ just ws → writes-types ws ≡ bs
    into-result p x y (val-jubjub-point point) declared bound computed rewrite declared
      with coordsJ point
    ... | _ , _ = trans (write-types-eq computed) (just-injective bound)
    into-result p x y (val-secp256k1-point point) declared bound computed rewrite declared
      with mapped-bind-success (coordsK1 point) (λ { (a , b) → val-secp256k1-base a , val-secp256k1-base b }) _ computed
    ... | (_ , _) , _ , written = trans (write-types-eq written) (just-injective bound)
    into-result p x y (val-secp256r1-point point) declared bound computed rewrite declared
      with mapped-bind-success (coordsP point) (λ { (a , b) → val-secp256r1-base a , val-secp256r1-base b }) _ computed
    ... | (_ , _) , _ , written = trans (write-types-eq written) (just-injective bound)
    into-result p x y (val-curve25519-point point) declared bound computed rewrite declared
      with coordsC point
    ... | _ , _ = trans (write-types-eq computed) (just-injective bound)
    into-result p x y (val-native _) _ () _
    into-result p x y (val-bytes _) _ () _
    into-result p x y (val-byte _) _ () _
    into-result p x y (val-bool _) _ () _
    into-result p x y (val-accumulator _) _ () _
    into-result p x y (val-jubjub-scalar _) _ () _
    into-result p x y (val-secp256k1-base _) _ () _
    into-result p x y (val-secp256k1-scalar _) _ () _
    into-result p x y (val-secp256r1-base _) _ () _
    into-result p x y (val-secp256r1-scalar _) _ () _
    into-result p x y (val-curve25519-base _) _ () _
    into-result p x y (val-curve25519-scalar _) _ () _

  into-coordinates-types : ∀ p x y → Rule sig Γ m (into-coordinates p (x , y))
  into-coordinates-types p x y declared computed with bind-success (ty sig Γ p) _ declared
  ... | t , known , bound with operand sig Γ m p store known
  ...   | v , seen , refl = into-result p x y v seen bound computed

  private
    from-result : ∀ x y o a b {bs ws}
      → typeof b ≡ typeof a
      → resolve m x ≡ just a → resolve m y ≡ just b
      → (from-base (typeof a) >>= one sig Γ o) ≡ just bs
      → compute m (from-coordinates (x , y) o) ≡ just ws → writes-types ws ≡ bs
    from-result x y o (val-native a) (val-native b) _ rx ry bound computed rewrite rx | ry
      with mapped-bind-success (fromCoordsJ a b) val-jubjub-point (write o) computed
    ... | q , _ , written = fixed (write-type o (val-jubjub-point q) refl written) bound
    from-result x y o (val-secp256k1-base a) (val-secp256k1-base b) _ rx ry bound computed rewrite rx | ry
      with mapped-bind-success (fromCoordsK1 a b) val-secp256k1-point (write o) computed
    ... | q , _ , written = fixed (write-type o (val-secp256k1-point q) refl written) bound
    from-result x y o (val-secp256r1-base a) (val-secp256r1-base b) _ rx ry bound computed rewrite rx | ry
      with mapped-bind-success (fromCoordsP a b) val-secp256r1-point (write o) computed
    ... | q , _ , written = fixed (write-type o (val-secp256r1-point q) refl written) bound
    from-result x y o (val-curve25519-base a) (val-curve25519-base b) _ rx ry bound computed rewrite rx | ry
      with mapped-bind-success (fromCoordsC a b) val-curve25519-point (write o) computed
    ... | q , _ , written = fixed (write-type o (val-curve25519-point q) refl written) bound
    from-result x y o (val-bytes _) _ _ _ _ () _
    from-result x y o (val-byte _) _ _ _ _ () _
    from-result x y o (val-bool _) _ _ _ _ () _
    from-result x y o (val-accumulator _) _ _ _ _ () _
    from-result x y o (val-jubjub-point _) _ _ _ _ () _
    from-result x y o (val-jubjub-scalar _) _ _ _ _ () _
    from-result x y o (val-secp256k1-point _) _ _ _ _ () _
    from-result x y o (val-secp256k1-scalar _) _ _ _ _ () _
    from-result x y o (val-secp256r1-point _) _ _ _ _ () _
    from-result x y o (val-secp256r1-scalar _) _ _ _ _ () _
    from-result x y o (val-curve25519-point _) _ _ _ _ () _
    from-result x y o (val-curve25519-scalar _) _ _ _ _ () _

  from-coordinates-types : ∀ x y o → Rule sig Γ m (from-coordinates (x , y) o)
  from-coordinates-types x y o declared computed with bind-success (ty sig Γ x) _ declared
  ... | t , tx , rest with bind-success (expect sig Γ t y) _ rest
  ...   | _ , ey , bound with operand sig Γ m x store tx | expect-operand sig Γ m y t store ey
  ...     | a , rx , refl | b , ry , same = from-result x y o a b same rx ry bound computed
