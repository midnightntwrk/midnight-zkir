{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitProperties (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Circuit ⋯
open import zkir-v4.Operations ⋯ using (guardD; _≟LFr_)
open import zkir-v4.Syntax ⋯

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Product using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import zkir-v4.Validation ⋯ using (validate)

private
  just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  just-injective refl = refl

  bind-success : ∀ {A B : Set} (a : Maybe A) (f : A → Maybe B) {b}
               → (a >>= f) ≡ just b
               → Σ A λ x → (a ≡ just x) × (f x ≡ just b)
  bind-success nothing _ ()
  bind-success (just x) _ ok = x , refl , ok

  guard-success : ∀ {P A : Set} (d : Dec P) (a : Maybe A) {x}
                → guardD d a ≡ just x → P × (a ≡ just x)
  guard-success (yes p) _ ok = p , ok
  guard-success (no _) _ ()

  finish-state : ∀ src w st st′
                 → finish-commitment src w st ≡ just st′
                 → st ≡ st′
  finish-state src w st st′ eq with IrSource.do-communications-commitment src
  ... | false = just-injective eq
  ... | true with CircuitWitness.comm-commitment w
  ...   | nothing with eq
  ...     | ()
  finish-state src w st st′ eq | true | just (c , r)
    with guard-success (c ≟ᶠ transient-commit
          (encode-inputs (CircuitState.mem st) (IrSource.inputs src) ++ encode-outputs st) r)
          (just st) eq
  ... | _ , ok = just-injective ok

finish-public-inputs : ∀ {src w st st′}
                         → finishᶜ src w st ≡ just st′
                         → full-public-inputsᶜ st′ ≡ CircuitWitness.full-pis w
finish-public-inputs {src} {w} {st} {st′} eq
  with guard-success (full-public-inputsᶜ st ≟LFr CircuitWitness.full-pis w) _ eq
... | public-ok , rest with finish-state src w st st′ rest
...   | refl = public-ok

satisfying-public-inputs : ∀ {src w st} → satisfies src w st
                          → accumulator-pisᶜ st ++ CircuitState.pis st ≡ CircuitWitness.full-pis w
satisfying-public-inputs {src} {w} eq
  with bind-success (synth src) (λ c → check-witness c w) eq
... | mk-circuit source constraints , _ , circuit-ok
  with bind-success (initᶜ source w)
         (λ initial → runᶜ source w initial constraints >>= finishᶜ source w) circuit-ok
...   | initial , _ , init-ok
  with bind-success (runᶜ source w initial constraints) (finishᶜ source w) init-ok
...     | before-finish , _ , finish-ok = finish-public-inputs {src = source} {w = w} {st = before-finish} finish-ok

-- A trace records every satisfied constraint at the point where its
-- operands are in scope.  Its constructors use the local chip contract.
data Trace (src : IrSource) (w : CircuitWitness)
           : CircuitState → List Constraint → CircuitState → Set where
  end : ∀ {st} → Trace src w st [] st
  next : ∀ {st st′ final c cs}
         → stepᶜ src w st c ≡ just st′
         → Trace src w st′ cs final
         → Trace src w st (c ∷ cs) final

run→trace : ∀ {src w st final} cs → runᶜ src w st cs ≡ just final → Trace src w st cs final
run→trace [] eq with just-injective eq
... | refl = end
run→trace {src} {w} {st} (c ∷ cs) eq
  with bind-success (stepᶜ src w st c) (λ st′ → runᶜ src w st′ cs) eq
... | _ , step-ok , rest-ok = next step-ok (run→trace cs rest-ok)

trace→run : ∀ {src w st final cs} → Trace src w st cs final → runᶜ src w st cs ≡ just final
trace→run end = refl
trace→run (next step-ok rest) rewrite step-ok = trace→run rest

record SatisfiedRun (src : IrSource) (w : CircuitWitness) (target : CircuitState) : Set where
  field
    validated : validate src ≡ true
    start : CircuitState
    initialized : initᶜ src w ≡ just start
    path : Trace src w start (map lower (IrSource.instructions src)) target

satisfying-run : ∀ src w target → satisfies src w target → SatisfiedRun src w target
satisfying-run src w target accepted with validate src in valid
... | false with () ← accepted
satisfying-run src w target accepted | true
  with bind-success (initᶜ src w)
       (λ start → runᶜ src w start (map lower (IrSource.instructions src)) >>= finishᶜ src w) accepted
... | start , initialized , checked
  with bind-success (runᶜ src w start (map lower (IrSource.instructions src))) (finishᶜ src w) checked
...   | before-finish , ran , finished
  with guard-success (full-public-inputsᶜ before-finish ≟LFr CircuitWitness.full-pis w) _ finished
...     | _ , committed with finish-state src w before-finish target committed
...       | refl = record
  { validated = valid ; start = start ; initialized = initialized
  ; path = run→trace (map lower (IrSource.instructions src)) ran
  }
