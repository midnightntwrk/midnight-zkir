{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SegmentLeaf (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (guard-pass; shared-forward; write-backward)
open import zkir-v4.CircuitProperties ⋯ using
  (Trace; next; end; trace→run; SatisfiedRun; satisfying-run)
open import zkir-v4.Operations ⋯ using (Mem; ∅; ins; _≟LFr_)
open import zkir-v4.Protocol ⋯ using (instance-fields)
open import zkir-v4.SegmentSource ⋯
open import zkir-v4.SequentialSource ⋯ using
  (active; initial-state; install; declared-native; declared-accumulator)
open import zkir-v4.Syntax ⋯ using (IrSource; _⦂_; var; imm; add)
open import zkir-v4.Types ⋯ using (native; accumulator; val-native; val-accumulator)
open import zkir-v4.Validation ⋯ using (validate)

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (∷-injectiveʳ)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (∃; _,_; _×_)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

private
  leaf-mem : Fr → Fr → Accumulator → Mem
  leaf-mem c a carried = ins (carry-id lhs) (val-accumulator carried)
    (ins x (val-native a) (ins ctx (val-native c) ∅))

  leaf-declared : ∀ w {m} → declare w ∅ leaf-inputs ≡ just m →
    ∃ λ c → ∃ λ a → ∃ λ carried → m ≡ leaf-mem c a carried
  leaf-declared w ok with declared-native w ∅ ctx
    (x ⦂ native ∷ carry-id lhs ⦂ accumulator ∷ []) ok
  ... | c , first with declared-native w (ins ctx (val-native c) ∅) x
    (carry-id lhs ⦂ accumulator ∷ []) first
  ...   | a , second with declared-accumulator w
    (ins x (val-native a) (ins ctx (val-native c) ∅)) (carry-id lhs) [] second
  ...     | carried , done = c , a , carried , sym (just-injective done)

  leaf-start : ∀ src w st → IrSource.inputs src ≡ leaf-inputs →
    IrSource.do-communications-commitment src ≡ false →
    initᶜ src w ≡ just st →
    ∃ λ c → ∃ λ a → ∃ λ carried → st ≡ initial-state w (leaf-mem c a carried)
  leaf-start src w st inputs no-commit initialized rewrite inputs | no-commit
    with declare w ∅ leaf-inputs in declared
  ... | nothing with () ← initialized
  leaf-start src w st inputs no-commit initialized | just m
    with leaf-declared w declared
  ... | c , a , carried , refl = c , a , carried , sym (just-injective initialized)

  idle-path : ∀ keys w c a carried {final} →
    Trace (source keys idle) w (initial-state w (leaf-mem c a carried))
      (map lower (IrSource.instructions (source keys idle))) final →
    CircuitState.pis final ≡ observed-fields 0 (CircuitWitness.binding-input w) c a a
  idle-path keys w c a carried (next published rest)
    rewrite active with refl ← just-injective published
    with next refl end ← rest = refl

  tick-path : ∀ keys w c a carried {final} →
    Trace (source keys tick) w (initial-state w (leaf-mem c a carried))
      (map lower (IrSource.instructions (source keys tick))) final →
    CircuitState.pis final ≡ observed-fields 1 (CircuitWitness.binding-input w) c a (a +ᶠ 1ᶠ)
  tick-path keys w c a carried (next added (next published rest))
    with refl ← write-backward true w (initial-state w (leaf-mem c a carried))
      ((z , val-native (a +ᶠ 1ᶠ)) ∷ []) added
    rewrite active with refl ← just-injective published
    with next refl end ← rest = refl

  fields-relation : ∀ n binding c a b c′ a′ b′ →
    observed-fields n binding c′ a′ b′ ≡ fields n c a b →
    (a′ ≡ a) × (b′ ≡ b)
  fields-relation n binding c a b c′ a′ b′ eq
    with ∷-injectiveʳ (∷-injectiveʳ eq)
  ... | refl = refl , refl

idle-observe : ∀ keys w final c a b →
  satisfies (source keys idle) w final →
  CircuitState.pis final ≡ fields (steps idle) c a b → b ≡ a
idle-observe keys w final c a b sat fields-ok
  with satisfying-run (source keys idle) w final sat
... | record { start = st ; initialized = initialized ; path = path }
  with leaf-start (source keys idle) w st refl refl initialized
... | c′ , a′ , carried , refl
  with fields-relation 0 (CircuitWitness.binding-input w) c a b c′ a′ a′
    (trans (sym (idle-path keys w c′ a′ carried path)) fields-ok)
... | refl , refl = refl

tick-observe : ∀ keys w final c a b →
  satisfies (source keys tick) w final →
  CircuitState.pis final ≡ fields (steps tick) c a b → b ≡ a +ᶠ 1ᶠ
tick-observe keys w final c a b sat fields-ok
  with satisfying-run (source keys tick) w final sat
... | record { start = st ; initialized = initialized ; path = path }
  with leaf-start (source keys tick) w st refl refl initialized
... | c′ , a′ , carried , refl
  with fields-relation 1 (CircuitWitness.binding-input w) c a b c′ a′ (a′ +ᶠ 1ᶠ)
    (trans (sym (tick-path keys w c′ a′ carried path)) fields-ok)
... | refl , refl = refl

private
  leaf-witness : Mem → List Fr → Accumulator → CircuitWitness
  leaf-witness m statement carried =
    mk-witness m (instance-fields (carried ∷ []) statement) 0ᶠ nothing []

  leaf-final : CircuitState → List Fr → Accumulator → CircuitState
  leaf-final st statement carried = record st { pis = statement ; accs = carried ∷ [] }

  assemble : ∀ src w first final →
    validate src ≡ true → IrSource.do-communications-commitment src ≡ false →
    initᶜ src w ≡ just first →
    Trace src w first (map lower (IrSource.instructions src)) final →
    full-public-inputsᶜ final ≡ CircuitWitness.full-pis w →
    satisfies src w final
  assemble src w first final valid no-commit initialized path full-ok
    rewrite valid | initialized | trace→run path | no-commit =
    guard-pass (full-public-inputsᶜ final ≟LFr CircuitWitness.full-pis w) full-ok (just final)

idle-witness : ∀ keys c a carried →
  ∃ λ w → ∃ λ final → satisfies (source keys idle) w final ×
    CircuitState.pis final ≡ fields (steps idle) c a a ×
    CircuitState.accs final ≡ carried ∷ [] ×
    CircuitWitness.full-pis w ≡ instance-fields (carried ∷ []) (fields (steps idle) c a a)
idle-witness keys c a carried =
  w , final , assemble src w first final refl refl refl path refl , refl , refl , refl
  where
  statement = fields 0 c a a
  src = source keys idle
  m = leaf-mem c a carried
  w = leaf-witness m statement carried
  first = initial-state w m
  published = record first { pis = statement }
  final = leaf-final first statement carried

  publish-ok : stepᶜ src w first (lower (publish 0 x)) ≡ just published
  publish-ok rewrite active = refl

  path : Trace src w first (map lower (IrSource.instructions src)) final
  path = next publish-ok (next refl end)

tick-witness : ∀ keys c a carried →
  ∃ λ w → ∃ λ final → satisfies (source keys tick) w final ×
    CircuitState.pis final ≡ fields (steps tick) c a (a +ᶠ 1ᶠ) ×
    CircuitState.accs final ≡ carried ∷ [] ×
    CircuitWitness.full-pis w ≡ instance-fields (carried ∷ []) (fields (steps tick) c a (a +ᶠ 1ᶠ))
tick-witness keys c a carried =
  w , final , assemble src w first final refl refl refl path refl , refl , refl , refl
  where
  statement = fields 1 c a (a +ᶠ 1ᶠ)
  src = source keys tick
  m = leaf-mem c a carried
  w = leaf-witness m statement carried
  first = initial-state w m
  added = install first z (val-native (a +ᶠ 1ᶠ))
  published = record added { pis = statement }
  final = leaf-final added statement carried

  add-ok : stepᶜ src w first (lower (add (var x) (imm 1ᶠ) z)) ≡ just added
  add-ok = shared-forward src w first (add (var x) (imm 1ᶠ) z)
    ((z , val-native (a +ᶠ 1ᶠ)) ∷ []) refl (inj₁ refl , tt)

  publish-ok : stepᶜ src w added (lower (publish 1 z)) ≡ just published
  publish-ok rewrite active = refl

  path : Trace src w first (map lower (IrSource.instructions src)) final
  path = next add-ok (next publish-ok (next refl end))
