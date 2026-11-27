{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerMemory (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯
open import zkir-v4.SemanticsProperties ⋯ using (Trace; done; next; AcceptedRun; preprocess-inversion)
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯
open import zkir-v4.ProducerStep ⋯ public
open import zkir-v4.InputProperties ⋯
open import zkir-v4.Encoding ⋯ using (decode)
open import zkir-v4.EncodingProperties ⋯ using (decode-typed)
open import zkir-v4.Circuit ⋯ using (declared-value)
open import zkir-v4.CircuitProof ⋯ using (honest-witness; apply)
open import zkir-v4.CircuitInputs ⋯ using (InitialInputsAgree; Matches)
open import zkir-v4.CommitmentInputs ⋯ using (InputFrame)
open import zkir-v4.CircuitBridge ⋯ using (WriteAgreement; Agrees)
open import zkir-v4.CircuitEffects ⋯ using (ReadValue)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; take; drop; length; map)
open import Data.List.Properties using (length-replicate)
import Data.Nat
open import Function using (_∘_)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []∀; _∷_ to _∷∀_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; ∃)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

data TypedTrace {p s final} : ∀ {st is} → Env → Trace p s st is final → Set where
  typed-done : ∀ {Γ} → StoreTyped Γ (State.mem final) → TypedTrace Γ done
  typed-next : ∀ {i is st mid Γ Γ′ bs} {ok : step p s st i ≡ just mid}
    {rest : Trace p s mid is final}
    → StoreTyped Γ (State.mem st)
    → bindings (IrSource.outputs s) Γ i ≡ just bs
    → (writes : StepWrites st i mid bs)
    → WriteFrame Γ Γ′ (State.mem st) (State.mem mid) (StepWrites.values writes)
    → TypedTrace Γ′ rest → TypedTrace Γ (next {i = i} {st = st} ok rest)

trace-store : ComputeTypes → ∀ {p s st is final} (tr : Trace p s st is final) Γ {Γ′}
  → StoreTyped Γ (State.mem st) → fold-check (producer-step (IrSource.outputs s)) Γ is ≡ just Γ′
  → TypedTrace Γ tr
trace-store types done Γ typed _ = typed-done typed
trace-store types {p} {s} (next {i} {is} {st} {mid} ok tail) Γ typed checked
  with fold-cons (producer-step (IrSource.outputs s)) Γ i is checked
... | Γ′ , head , rest with bind-success (bindings (IrSource.outputs s) Γ i) _ head
... | bs , bindings-ok , fresh-ok
  with step-writes types p s st i mid Γ typed bindings-ok ok
... | ws with writing-frame ws fresh-ok
  where
  writing-frame : (ws : StepWrites st i mid bs) → fold-check fresh Γ bs ≡ just Γ′
    → WriteFrame Γ Γ′ (State.mem st) (State.mem mid) (StepWrites.values ws)
  writing-frame ws fresh-ok =
    subst (λ memory → WriteFrame Γ Γ′ (State.mem st) memory (StepWrites.values ws))
      (sym (StepWrites.memory ws))
      (write-frame Γ (State.mem st) (StepWrites.values ws) typed
        (trans (cong (fold-check fresh Γ) (StepWrites.types ws)) fresh-ok))
... | frame = typed-next {i = i} {st = st} {ok = ok} typed bindings-ok ws frame
  (trace-store types tail Γ′ (WriteFrame.typed-after frame) rest)

trace-extends : ∀ {p s st is final} {tr : Trace p s st is final} {Γ}
  → TypedTrace Γ tr → Extends Γ (State.mem st) (State.mem final)
trace-extends (typed-done _) _ _ _ = refl
trace-extends (typed-next _ _ _ frame rest) id t found =
  trans (trace-extends rest id t (WriteFrame.keeps-types frame id t found))
        (WriteFrame.extends frame id t found)

private
  align-writes : ∀ p final checked ws →
    All (λ { (id , v) → State.mem final id ≡ just v }) ws →
    WriteAgreement checked (honest-witness p final) ws
  align-writes p final false ws found = tt
  align-writes p final true [] []∀ = tt
  align-writes p final true ((id , v) ∷ ws) (found ∷∀ rest) =
    inj₂ found , align-writes p final true ws rest

  extended-writes : ∀ Γ m m′ (ws : List (Identifier × IrValue)) → Extends Γ m m′
    → All (λ { (id , v) → (m id ≡ just v) × (type-of Γ id ≡ just (typeof v)) }) ws
    → All (λ { (id , v) → m′ id ≡ just v }) ws
  extended-writes Γ m m′ [] grows []∀ = []∀
  extended-writes Γ m m′ ((id , v) ∷ ws) grows ((stored , typed) ∷∀ rest) =
    trans (grows id (typeof v) typed) stored ∷∀ extended-writes Γ m m′ ws grows rest

computed-agreement : ∀ {p s st i after is final Γ Γ′ bs}
  {tail : Trace p s after is final} (ws : StepWrites st i after bs)
  → WriteFrame Γ Γ′ (State.mem st) (State.mem after) (StepWrites.values ws)
  → TypedTrace Γ′ tail → ∀ checked values → compute (State.mem st) i ≡ just values
  → WriteAgreement checked (honest-witness p final) values
computed-agreement {p} {s} {st} {i} {after} {is} {final} {Γ} {Γ′} ws frame tail checked values ok
  rewrite StepWrites.computed ws values ok = align-writes p final checked (StepWrites.values ws)
    (extended-writes Γ′ (State.mem after) (State.mem final) (StepWrites.values ws)
      (trace-extends tail) (WriteFrame.written frame))

private
  singleton-bound : ∀ {Γ} {m : Mem} {ws : List (Identifier × IrValue)} {id t} →
    All (λ { (k , v) → (m k ≡ just v) × (type-of Γ k ≡ just (typeof v)) }) ws
    → writes-types ws ≡ (id ⦂ t) ∷ []
    → type-of Γ id ≡ just t
  singleton-bound {ws = (_ , _) ∷ []} ((_ , typed) ∷∀ []∀) refl = typed

  keeps-singleton : ∀ {p s st i after is final Γ Γ′ bs id t} {tail : Trace p s after is final}
    (ws : StepWrites st i after bs)
    → WriteFrame Γ Γ′ (State.mem st) (State.mem after) (StepWrites.values ws)
    → TypedTrace Γ′ tail → bs ≡ (id ⦂ t) ∷ []
    → State.mem final id ≡ State.mem after id
  keeps-singleton {after = after} {Γ′ = Γ′} {id = id} {t = t} ws frame tail shape =
    trace-extends tail id t (singleton-bound {Γ = Γ′} {m = State.mem after} {ws = StepWrites.values ws}
      (WriteFrame.written frame) (trans (StepWrites.types ws) shape))

  guarded-read : ∀ st g t id active raw v
    (install : IrValue → State)
    → eval-guard (State.mem st) g ≡ just active
    → ReadValue active t raw v
    → (eval-guard (State.mem st) g >>= λ b →
        if b then (decode t (take (encoded-len t) raw) >>= λ u → just (install u))
             else just (out1 st id (default-val t)))
      ≡ just (if active then install v else out1 st id v)
  guarded-read st g t id false raw v install bit refl rewrite bit = refl
  guarded-read st g t id true raw v install bit decoded rewrite bit | decoded = refl

  state-written : ∀ {st after : State} id v → State.mem after ≡ ins id v (State.mem st)
    → State.mem after id ≡ just v
  state-written {st} id v memory =
    trans (cong (λ m → m id) memory) (lookup-inserted (State.mem st) id v)

public-agreement : ∀ {p s st after is final Γ Γ′ bs g t id} {tail : Trace p s after is final}
  → bindings (IrSource.outputs s) Γ (public-input g t id) ≡ just bs
  → step p s st (public-input g t id) ≡ just after
  → (ws : StepWrites st (public-input g t id) after bs)
  → WriteFrame Γ Γ′ (State.mem st) (State.mem after) (StepWrites.values ws)
  → TypedTrace Γ′ tail → ∀ active v → eval-guard (State.mem st) g ≡ just active
  → ReadValue active t (State.pto-rem st) v
  → (State.mem final id ≡ just v) × (typeof v ≡ t)
public-agreement {p} {s} {st} {after} {is} {final} {Γ} {Γ′} {bs} {g} {t} {id}
  binds ok ws frame tail active v bit read =
  trans (keeps-singleton {p = p} {s = s} {Γ = Γ} {t = t} ws frame tail
          (sym (final-bindings {xs = guard-ty (IrSource.outputs s) Γ g} binds)))
        (state-written {st = st} {after = after} id v (trans (cong State.mem (just-injective (trans (sym ok) exact))) (mem active))) ,
  read-typed active t (State.pto-rem st) v read
  where
  install : IrValue → State
  install u = record (out1 st id u) { pto-rem = drop (encoded-len t) (State.pto-rem st) }
  exact = guarded-read st g t id active (State.pto-rem st) v install bit read
  mem : ∀ b → State.mem (if b then install v else out1 st id v) ≡ ins id v (State.mem st)
  mem false = refl
  mem true = refl

private-agreement : ∀ {p s st after is final Γ Γ′ bs g t id} {tail : Trace p s after is final}
  → bindings (IrSource.outputs s) Γ (private-input g t id) ≡ just bs
  → step p s st (private-input g t id) ≡ just after
  → (ws : StepWrites st (private-input g t id) after bs)
  → WriteFrame Γ Γ′ (State.mem st) (State.mem after) (StepWrites.values ws)
  → TypedTrace Γ′ tail → ∀ active v → eval-guard (State.mem st) g ≡ just active
  → ReadValue active t (State.priv-rem st) v
  → (State.mem final id ≡ just v) × (typeof v ≡ t)
private-agreement {p} {s} {st} {after} {is} {final} {Γ} {Γ′} {bs} {g} {t} {id}
  binds ok ws frame tail active v bit read =
  trans (keeps-singleton {p = p} {s = s} {Γ = Γ} {t = t} ws frame tail
          (sym (final-bindings {xs = guard-ty (IrSource.outputs s) Γ g} binds)))
        (state-written {st = st} {after = after} id v (trans (cong State.mem (just-injective (trans (sym ok) exact))) (mem active))) ,
  read-typed active t (State.priv-rem st) v read
  where
  install : IrValue → State
  install u = record (out1 st id u) { priv-rem = drop (encoded-len t) (State.priv-rem st) }
  exact = guarded-read st g t id active (State.priv-rem st) v install bit read
  mem : ∀ b → State.mem (if b then install v else out1 st id v) ≡ ins id v (State.mem st)
  mem false = refl
  mem true = refl

private
  accumulator-written : ∀ st after id acc (result : Maybe Accumulator)
    → result ≡ just acc
    → (result >>= λ a → just (out1 st id (val-accumulator a))) ≡ just after
    → State.mem after id ≡ just (val-accumulator acc)
  accumulator-written st after id acc .(just acc) refl ok =
    state-written {st = st} {after = after} id (val-accumulator acc) (cong State.mem (sym (just-injective ok)))

prepare-agreement : ∀ {p s st after is final Γ Γ′ bs g h ops pr id} {tail : Trace p s after is final}
  → bindings (IrSource.outputs s) Γ (prepare-verification g h ops pr id) ≡ just bs
  → step p s st (prepare-verification g h ops pr id) ≡ just after
  → (ws : StepWrites st (prepare-verification g h ops pr id) after bs)
  → WriteFrame Γ Γ′ (State.mem st) (State.mem after) (StepWrites.values ws)
  → TypedTrace Γ′ tail → ∀ acc → prepare-result s st g h ops pr ≡ just acc
  → Agrees (honest-witness p final) id (val-accumulator acc)
prepare-agreement {p} {s} {st} {after} {is} {final} {Γ} {Γ′} {bs} {g} {h} {ops} {pr} {id}
  binds ok ws frame tail acc result = inj₂
  (trans (keeps-singleton {p = p} {s = s} {Γ = Γ} {t = accumulator} ws frame tail (sym (prepare-binding (IrSource.outputs s) Γ g h ops pr id binds)))
         (accumulator-written st after id acc (prepare-result s st g h ops pr) result ok))

fold-agreement : ∀ {p s st after is final Γ Γ′ bs ops id} {tail : Trace p s after is final}
  → bindings (IrSource.outputs s) Γ (accumulate ops id) ≡ just bs
  → step p s st (accumulate ops id) ≡ just after
  → (ws : StepWrites st (accumulate ops id) after bs)
  → WriteFrame Γ Γ′ (State.mem st) (State.mem after) (StepWrites.values ws)
  → TypedTrace Γ′ tail → ∀ acc → fold-result (State.mem st) ops ≡ just acc
  → Agrees (honest-witness p final) id (val-accumulator acc)
fold-agreement {p} {s} {st} {after} {is} {final} {Γ} {Γ′} {bs} {ops} {id}
  binds ok ws frame tail acc result = inj₂
  (trans (keeps-singleton {p = p} {s = s} {Γ = Γ} {t = accumulator} ws frame tail (sym (fold-binding (IrSource.outputs s) Γ ops id binds)))
         (accumulator-written st after id acc (fold-result (State.mem st) ops) result ok))

private
  declared-matches : ∀ p final {ds} (vs : DeclaredValues ds)
    → All (λ { (id , v) → State.mem final id ≡ just v }) (declared-writes vs)
    → Matches (honest-witness p final) vs
  declared-matches p final []ᵈ []∀ = tt
  declared-matches p final (_∷ᵈ_ {ti = ti} v (_ , _ , vs)) (found ∷∀ rest) =
      match p final (TypedIdentifier.name ti) v found , declared-matches p final vs rest
    where
    match : ∀ p final id v → State.mem final id ≡ just v → declared-value (honest-witness p final) id ≡ v
    match p final id v found rewrite found = refl

  declared-frame : ∀ Γ start final {ds} (vs : DeclaredValues ds) → Extends Γ start final
    → All (λ { (id , v) → (start id ≡ just v) × (type-of Γ id ≡ just (typeof v)) }) (declared-writes vs)
    → InputFrame ds start final
  declared-frame Γ start final []ᵈ grows []∀ = []∀
  declared-frame Γ start final (_∷ᵈ_ {ti = ti} v (_ , _ , vs)) grows ((_ , typed) ∷∀ rest) =
    grows (TypedIdentifier.name ti) (typeof v) typed ∷∀ declared-frame Γ start final vs grows rest

initial-agreement : ∀ s p start final Γ → InitialStore s p Γ (State.mem start)
  → Extends Γ (State.mem start) (State.mem final) → InitialInputsAgree s p (honest-witness p final)
initial-agreement s p start final Γ initial grows =
  values , InitialStore.raw initial ,
  declared-matches p final values
    (extended-writes Γ (State.mem start) (State.mem final) (declared-writes values)
      grows (WriteFrame.written (InitialStore.frame initial)))
  where values = InitialStore.values initial

initial-input-frame : ∀ s p start final Γ → InitialStore s p Γ (State.mem start)
  → Extends Γ (State.mem start) (State.mem final)
  → InputFrame (IrSource.inputs s) (State.mem start) (State.mem final)
initial-input-frame s p start final Γ initial grows =
  declared-frame Γ (State.mem start) (State.mem final) (InitialStore.values initial) grows
    (WriteFrame.written (InitialStore.frame initial))
