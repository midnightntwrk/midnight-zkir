{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.AccumulatorObligations (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.AccumulatorEffects ⋯
open import zkir-v4.AccumulatorLifecycle ⋯ as Lifecycle using
  (Pending; AccWalk; accepted-acc-walk; prepare-pending; fold-pending; acc-disposition; retained; discharged; fold-input)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitAccumulatorFrame ⋯ using (CircuitFrame; circuit-step-frame; circuit-init-store)
open import zkir-v4.CircuitProperties ⋯ using (SatisfiedRun; Trace; end; next)
open import zkir-v4.Operations ⋯ using (resolve-acc; resolve-accs)
open import zkir-v4.Producer ⋯ using (Env; Producer; bindings; fold-check; fresh; producer-step; type-of)
open import zkir-v4.ProducerStep ⋯ using (prepare-binding; fold-binding)
open import zkir-v4.ProducerStore ⋯ using
  (bind-success; fold-cons; infer-success; fresh-success; type-inserted; StoreTyped)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯ using (accumulator; val-accumulator)
open import zkir-v4.Validation ⋯ using (AccUses; Uses; acc-step)

open import Data.Bool using (true)
open import Data.Bool.Properties using (T?)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.All.Properties using (++⁻ˡ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (∃; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no)

PreparationClaim : IrSource → Set₁
PreparationClaim src = ∀ {st g hash ops pr out st′} → Prepared src st g hash ops pr out st′ → Set

TraceEvent : IrSource → CircuitWitness → Set₁
TraceEvent src w =
  ∀ {st st′} i → stepᶜ src w st (lower i) ≡ just st′ → Set

data Occurs {src w} (Event : TraceEvent src w) :
    ∀ {st final} is → Trace src w st (map lower is) final → Set where
  at-head : ∀ {st st′ final i is}
    {ok : stepᶜ src w st (lower i) ≡ just st′}
    {rest : Trace src w st′ (map lower is) final} →
    Event {st} {st′} i ok → Occurs Event (i ∷ is) (next ok rest)
  in-tail : ∀ {st st′ final i is}
    {ok : stepᶜ src w st (lower i) ≡ just st′}
    {rest : Trace src w st′ (map lower is) final} →
    Occurs Event is rest → Occurs Event (i ∷ is) (next ok rest)

data ConsumptionAt {src w} (a : Accumulator) {st st′} :
    ∀ i → stepᶜ src w st (lower i) ≡ just st′ → Set where
  fold-operand : ∀ {ops out} {ok : stepᶜ src w st (fold-accs ops out) ≡ just st′} →
    a ∈ Folded.inputs (fold-step src w st ops out ok) → ConsumptionAt a (accumulate ops out) ok
  exposed-value : ∀ {op} {ok : stepᶜ src w st (publish-acc op) ≡ just st′} →
    Exposed.value (expose-step src w st op ok) ≡ a → ConsumptionAt a (verify-accumulator op) ok

Consumed : ∀ {src w st final} is →
  Trace src w st (map lower is) final → Accumulator → Set
Consumed {src} {w} is path a = Occurs (ConsumptionAt {src} {w} a) is path

ValidConsumptions : ∀ {src w st final} is →
  Trace src w st (map lower is) final → Set
ValidConsumptions is path = ∀ a → Consumed is path a → Valid a

private
  data EffectView : Instruction → Set where
    prep : ∀ g hash ops pr out → EffectView (prepare-verification g hash ops pr out)
    fold : ∀ ops out → EffectView (accumulate ops out)
    other : ∀ {i} → EffectView i

  effect-view : ∀ i → EffectView i
  effect-view (prepare-verification g hash ops pr out) = prep g hash ops pr out
  effect-view (accumulate ops out) = fold ops out
  effect-view _ = other

  PreparationStep : ∀ {src} → PreparationClaim src → ∀ {w st st′} (i : Instruction) →
    stepᶜ src w st (lower i) ≡ just st′ → Set
  PreparationStep {src} P {w} {st} i ok with effect-view i
  ... | prep g hash ops pr out =
    let e = prepared-step src w st g hash ops pr out ok in Prepared.active e ≡ true → P e
  ... | fold _ _ = ⊤
  ... | other = ⊤

PreparationsSatisfy : ∀ {src} → PreparationClaim src → ∀ {w st final} (is : List Instruction) →
  Trace src w st (map lower is) final → Set
PreparationsSatisfy P [] end = ⊤
PreparationsSatisfy {src} P {w} {st} (i ∷ is) (next {st′ = st′} ok rest) =
  PreparationStep {src} P {w} {st} {st′} i ok × PreparationsSatisfy P is rest

private
  zip-preparation : ∀ {src} {P Q R : PreparationClaim src}
    → (∀ {st g hash ops pr out st′} (e : Prepared src st g hash ops pr out st′) →
         Prepared.active e ≡ true → P e → Q e → R e)
    → ∀ {w st st′} i (ok : stepᶜ src w st (lower i) ≡ just st′)
    → PreparationStep {src} P {w} {st} {st′} i ok → PreparationStep {src} Q {w} {st} {st′} i ok
    → PreparationStep {src} R {w} {st} {st′} i ok
  zip-preparation {src} f {w} {st} i ok left right with effect-view i
  ... | prep g hash ops pr out = λ on → f (prepared-step src w st g hash ops pr out ok) on (left on) (right on)
  ... | fold _ _ = tt
  ... | other = tt

zip-preparations : ∀ {src} {P Q R : PreparationClaim src}
  → (∀ {st g hash ops pr out st′} (e : Prepared src st g hash ops pr out st′) →
       Prepared.active e ≡ true → P e → Q e → R e)
  → ∀ {w st final} is (path : Trace src w st (map lower is) final)
  → PreparationsSatisfy P is path → PreparationsSatisfy Q is path → PreparationsSatisfy R is path
zip-preparations f [] end _ _ = tt
zip-preparations {src} {P} {Q} {R} f {w} {st} (i ∷ is) (next {st′ = st′} ok rest) (p , ps) (q , qs) =
  zip-preparation {src} {P} {Q} {R} f {w} {st} {st′} i ok p q ,
  zip-preparations {src} {P} {Q} {R} f is rest ps qs

map-preparations : ∀ {src} {P Q : PreparationClaim src}
  → (∀ {st g hash ops pr out st′} (e : Prepared src st g hash ops pr out st′) →
       Prepared.active e ≡ true → P e → Q e)
  → ∀ {w st final} is (path : Trace src w st (map lower is) final)
  → PreparationsSatisfy P is path → PreparationsSatisfy Q is path
map-preparations {src} {P} {Q} f is path ps =
  zip-preparations {src} {P} {P} {Q} (λ e active p _ → f e active p) is path ps ps

InvalidInput : List Accumulator → Set
InvalidInput inputs = ∃ λ a → a ∈ inputs × ¬ Valid a

data BadFoldAt {src w st st′} : ∀ i → stepᶜ src w st (lower i) ≡ just st′ → Set where
  bad-fold : ∀ {ops out} {ok : stepᶜ src w st (fold-accs ops out) ≡ just st′} →
    let e = fold-step src w st ops out ok in
    Valid (Folded.output e) → InvalidInput (Folded.inputs e) → BadFoldAt {src} {w} {st} {st′} (accumulate ops out) ok

data BadFold {src w} : ∀ {st final} is → Trace src w st (map lower is) final → Set where
  fold-here : ∀ {st st′ final i is}
    {ok : stepᶜ src w st (lower i) ≡ just st′} {rest : Trace src w st′ (map lower is) final} →
    BadFoldAt {src} {w} {st} {st′} i ok → BadFold (i ∷ is) (next ok rest)
  fold-later : ∀ {st st′ final i is}
    {ok : stepᶜ src w st (lower i) ≡ just st′} {rest : Trace src w st′ (map lower is) final} →
    BadFold is rest → BadFold (i ∷ is) (next ok rest)

private
  all-valid-or-invalid : ∀ as → All Valid as ⊎ InvalidInput as
  all-valid-or-invalid [] = inj₁ All.[]
  all-valid-or-invalid (a ∷ as) with T? (pairing-valid a)
  ... | no invalid = inj₂ (a , here refl , invalid)
  ... | yes valid with all-valid-or-invalid as
  ...   | inj₁ rest = inj₁ (valid All.∷ rest)
  ...   | inj₂ (x , member , invalid) = inj₂ (x , there member , invalid)

  resolved-member : ∀ m ops {values op a} →
    resolve-accs m ops ≡ just values → op ∈ ops →
    resolve-acc m op ≡ just a → a ∈ values
  resolved-member m [] _ () _
  resolved-member m (x ∷ xs) found member value
    with bind-success (resolve-acc m x) (λ b → resolve-accs m xs >>= λ bs → just (b ∷ bs)) found
  ... | b , entry , remains with bind-success (resolve-accs m xs) (λ bs → just (b ∷ bs)) remains
  ...   | bs , resolved , shape with just-injective shape
  ...     | refl with member
  ...       | here refl = here (just-injective (trans (sym value) entry))
  ...       | there elsewhere = there (resolved-member m xs resolved elsewhere value)

  resolve-stored : ∀ m id a → m id ≡ just (val-accumulator a) → resolve-acc m (var id) ≡ just a
  resolve-stored m id a stored rewrite stored = refl

  list-output-type : ∀ sig Γ i out {Γ′} →
    (∀ {bs} → bindings sig Γ i ≡ just bs → (out ⦂ accumulator) ∷ [] ≡ bs) →
    producer-step sig Γ i ≡ just Γ′ → type-of Γ′ out ≡ just accumulator
  list-output-type sig Γ i out binding typed with bind-success (bindings sig Γ i) _ typed
  ... | _ , outputs , inserted with binding outputs
  ...   | refl with fold-cons fresh Γ (out ⦂ accumulator) [] inserted
  ...     | _ , fresh-out , final with fresh-success Γ out accumulator fresh-out | just-injective final
  ...       | refl , _ | refl = type-inserted Γ out accumulator

  PendingValid : AccUses → Env → CircuitState → Set
  PendingValid ledger Γ st = ∀ id a → Pending id ledger → type-of Γ id ≡ just accumulator →
    CircuitState.mem st id ≡ just (val-accumulator a) → Valid a

  FoldInputs : ∀ {src w st st′} (i : Instruction) → stepᶜ src w st (lower i) ≡ just st′ → Set
  FoldInputs {src} {w} {st} i ok with effect-view i
  ... | prep _ _ _ _ _ = ⊤
  ... | fold ops out = All Valid (Folded.inputs (fold-step src w st ops out ok))
  ... | other = ⊤

  OpeningValid : ∀ {src} → PreparationClaim src
  OpeningValid e = Valid (Prepared.opening e)

  step-obligations : ∀ src w st i st′ u u′ Γ Γ′
    → (ok : stepᶜ src w st (lower i) ≡ just st′)
    → producer-step (IrSource.outputs src) Γ i ≡ just Γ′
    → acc-step u i ≡ just u′
    → PendingValid u′ Γ′ st′
    → BadFoldAt {src} {w} {st} i ok ⊎
      (PreparationStep {src} OpeningValid {w} {st} i ok × FoldInputs {src} {w} {st} i ok)
  step-obligations src w st i st′ u _ Γ _ ok typed tracked after with effect-view i
  ... | prep g hash ops pr out =
    inj₂ ((λ _ → prepare-output) , tt)
    where
    e = prepared-step src w st g hash ops pr out ok
    prepare-output = after out (Prepared.opening e)
      (prepare-pending u {g = g} {hash = hash} {ops = ops} {proof = pr} tracked)
      (list-output-type (IrSource.outputs src) Γ (prepare-verification g hash ops pr out) out
        (prepare-binding (IrSource.outputs src) Γ g hash ops pr out) typed)
      (Prepared.stored e)
  ... | fold ops out with all-valid-or-invalid (Folded.inputs (fold-step src w st ops out ok))
  ...   | inj₁ good = inj₂ (tt , good)
  ...   | inj₂ invalid = inj₁ (bad-fold valid-output invalid)
    where
    e = fold-step src w st ops out ok
    valid-output = after out (Folded.output e)
      (fold-pending u {ops = ops} tracked)
      (list-output-type (IrSource.outputs src) Γ (accumulate ops out) out
        (fold-binding (IrSource.outputs src) Γ ops out) typed)
      (Folded.stored e)
  step-obligations src w st i st′ u _ Γ _ ok typed tracked after | other = inj₂ (tt , tt)

  pending-before : ∀ src w st i st′ u u′ Γ Γ′
    → (ok : stepᶜ src w st (lower i) ≡ just st′)
    → acc-step u i ≡ just u′
    → CircuitFrame st i st′ Γ Γ′
    → All Valid (CircuitState.accs st′)
    → PendingValid u′ Γ′ st′
    → FoldInputs {src} {w} {st} i ok
    → PendingValid u Γ st
  pending-before src w st i st′ u u′ Γ Γ′ ok checked frame exposed valid-after folds id a pending typed stored
    with acc-disposition id u i checked pending
  ... | retained kept = valid-after id a kept
    (CircuitFrame.keeps-types frame id accumulator typed)
    (trans (CircuitFrame.extends frame id accumulator typed) stored)
  ... | discharged with expose-step src w st (var id) ok
  ...   | e = subst Valid same (exposed-valid e exposed)
    where
    same = just-injective (trans (sym (Exposed.resolved e)) (resolve-stored (CircuitState.mem st) id a stored))
  pending-before src w st (accumulate ops out) st′ u u′ Γ Γ′ ok checked frame exposed valid-after folds id a pending typed stored
    | fold-input member _ = All.lookup folds
    (resolved-member (CircuitState.mem st) ops
      (Folded.resolved (fold-step src w st ops out ok)) member
      (resolve-stored (CircuitState.mem st) id a stored))

  before-exposures : ∀ {st i st′ Γ Γ′} → CircuitFrame st i st′ Γ Γ′ →
    All Valid (CircuitState.accs st′) → All Valid (CircuitState.accs st)
  before-exposures {st} frame valid with CircuitFrame.accs frame
  ... | suffix , _ , appended = ++⁻ˡ (CircuitState.accs st) {suffix} (subst (All Valid) appended valid)

  consumption-valid : ∀ {src w st st′ i a} {ok : stepᶜ src w st (lower i) ≡ just st′} →
    ConsumptionAt {src} {w} a i ok → FoldInputs {src} {w} {st} i ok →
    All Valid (CircuitState.accs st′) → Valid a
  consumption-valid (fold-operand member) folds _ = All.lookup folds member
  consumption-valid {src} {w} {st} {ok = ok} (exposed-value {op} same) _ exposed =
    subst Valid same (exposed-valid (expose-step src w st op ok) exposed)

  -- A suffix either contains a concrete bad fold or establishes the validity
  -- of each accumulator pending at its entry, as well as its active openings.
  walk-obligations : ∀ src w st final is (path : Trace src w st (map lower is) final)
    → ∀ u Γ {Γ′}
    → AccWalk u is
    → fold-check (producer-step (IrSource.outputs src)) Γ is ≡ just Γ′
    → StoreTyped Γ (CircuitState.mem st)
    → All Valid (CircuitState.accs final)
    → BadFold {src} {w} is path ⊎
      (PendingValid u Γ st × All Valid (CircuitState.accs st) ×
       PreparationsSatisfy OpeningValid is path × ValidConsumptions is path)
  walk-obligations src w st .st [] end u Γ (Lifecycle.done empty) typed store final-good =
    inj₂ ((λ id a pending _ _ → absent (subst (λ p → _ ∈ p) empty pending) {a = a}) , final-good , tt , λ _ ())
    where
    absent : ∀ {A : Set} {x : A} → x ∈ [] → ∀ {a} → Valid a
    absent ()
  walk-obligations src w st final (i ∷ is) (next {st′ = st′} ok tail) u Γ (Lifecycle.next {u′ = u′} tracked rest)
    typed store final-good
    with fold-cons (producer-step (IrSource.outputs src)) Γ i is typed
  ... | Γ′ , step-type , tail-types
    with circuit-step-frame src w st i st′ Γ store step-type ok
  ...   | frame
    with walk-obligations src w st′ final is tail u′ Γ′ rest tail-types (CircuitFrame.typed-after frame) final-good
  ...     | inj₁ bad = inj₁ (fold-later bad)
  ...     | inj₂ (pending , exposed , later , uses)
    with step-obligations src w st i st′ u u′ Γ Γ′ ok step-type tracked pending
  ...       | inj₁ bad = inj₁ (fold-here bad)
  ...       | inj₂ (active , folds) = inj₂
    (pending-before src w st i st′ u u′ Γ Γ′ ok tracked frame exposed pending folds ,
     before-exposures frame exposed ,
     (active , later) , λ
       { a (at-head event) → consumption-valid event folds exposed
       ; a (in-tail event) → uses a event })

obligations-or-bad-fold : ∀ src w final → Producer src →
  (run : SatisfiedRun src w final) → All Valid (CircuitState.accs final) →
  (PreparationsSatisfy (λ e → Valid (Prepared.opening e)) (IrSource.instructions src) (SatisfiedRun.path run) ×
   ValidConsumptions (IrSource.instructions src) (SatisfiedRun.path run)) ⊎
  BadFold {src} {w} (IrSource.instructions src) (SatisfiedRun.path run)
obligations-or-bad-fold src w final producer run final-good
  with infer-success src producer | accepted-acc-walk src (SatisfiedRun.validated run)
... | Γ , _ , inputs , checked | ledger , walk
  with walk-obligations src w (SatisfiedRun.start run) final (IrSource.instructions src) (SatisfiedRun.path run)
    ledger Γ walk checked (circuit-init-store src w inputs (SatisfiedRun.initialized run)) final-good
...   | inj₁ bad = inj₂ bad
...   | inj₂ (_ , _ , good) = inj₁ good

sound-or-bad-fold : ∀ src w final → Producer src →
  (run : SatisfiedRun src w final) → All Valid (CircuitState.accs final) →
  PreparationsSatisfy (λ e → Valid (Prepared.opening e)) (IrSource.instructions src) (SatisfiedRun.path run) ⊎
  BadFold {src} {w} (IrSource.instructions src) (SatisfiedRun.path run)
sound-or-bad-fold src w final producer run final-good
  with obligations-or-bad-fold src w final producer run final-good
... | inj₁ (good , _) = inj₁ good
... | inj₂ bad = inj₂ bad
