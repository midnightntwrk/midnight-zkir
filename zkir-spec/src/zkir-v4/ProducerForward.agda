{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.ProducerForward (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯
open import zkir-v4.Semantics ⋯ hiding (write)
open import zkir-v4.SemanticsProperties ⋯ using (Trace; done; next; AcceptedRun; preprocess-inversion)
open import zkir-v4.Producer ⋯
open import zkir-v4.ProducerStore ⋯
open import zkir-v4.ProducerMemory ⋯
open import zkir-v4.ProducerSupport ⋯
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (view)
open import zkir-v4.CircuitProof ⋯ using (honest-witness)
open import zkir-v4.CircuitEffects ⋯ using (PreparationForward)
open import zkir-v4.CircuitForward ⋯ using (forward-using; ReadyRun)
open import zkir-v4.ForwardShape ⋯
open import zkir-v4.CircuitInputs ⋯ using (init-forward-decoded; InitialInputsAgree; encode-installed-inputs)

open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

-- Conditions on the primitive invocations made by the accepted VM run.
ForwardDomains : ∀ {p s st is final} → Trace p s st is final → Set
ForwardDomains done = ⊤
ForwardDomains {s = s} (next {i = i} {st = st} _ tail) = ForwardDomain s st i × ForwardDomains tail

private
  cells-agree : ∀ {s p st i mid is final Γ Γ′ bs} {rest : Trace p s mid is final}
    → bindings (IrSource.outputs s) Γ i ≡ just bs
    → step p s st i ≡ just mid
    → (writes : StepWrites st i mid bs)
    → WriteFrame Γ Γ′ (State.mem st) (State.mem mid) (StepWrites.values writes)
    → TypedTrace Γ′ rest
    → WitnessCells s (honest-witness p final) st i
  cells-agree {s} {p} {st} {i} {mid} {is} {final} {Γ} {Γ′} {bs} binds ok ws frame tail = record
    { public-cell = λ { refl → public-agreement {p = p} {s = s} {Γ = Γ} binds ok ws frame tail }
    ; private-cell = λ { refl → private-agreement {p = p} {s = s} {Γ = Γ} binds ok ws frame tail }
    ; prepared-cell = λ { refl → prepare-agreement {p = p} {s = s} {Γ = Γ} binds ok ws frame tail }
    ; folded-cell = λ { refl → fold-agreement {p = p} {s = s} {Γ = Γ} binds ok ws frame tail }
    }

  supported-trace : ∀ {p s st is final Γ} {tr : Trace p s st is final}
    → TypedTrace Γ tr → ForwardDomains tr → Along (honest-witness p final) tr
  supported-trace (typed-done _) _ = tt
  supported-trace {p} {s} {final = final} {Γ = Γ}
    (typed-next {i = i} {st = st} {mid = mid} {ok = ok} {rest = rest} typed bindings-ok writes frame tail)
    (domain , later) =
    support-step {s = s} {p = p} {w = honest-witness p final} {st = st} {after = mid} {i = i} {Γ = Γ}
      typed bindings-ok ok (computed-agreement {p = p} {s = s} writes frame tail)
      (cells-agree {s = s} {p = p} {st = st} {i = i} {mid = mid} {Γ = Γ}
        {rest = rest} bindings-ok ok writes frame tail) domain ,
    supported-trace tail later

record HonestRun (src : IrSource) (p : ProofPreimage) (final : State)
                 (accepted : preprocess src p ≡ just final) : Set where
  private
    start = AcceptedRun.initial (preprocess-inversion {src} {p} accepted)
    w = honest-witness p final
  field
    inputs-agree : InitialInputsAgree src p w
    encoded-inputs : encode-inputs (State.mem start) (IrSource.inputs src) ≡ ProofPreimage.inputs p
    initialized : initᶜ src w ≡ just (view start (State.inner-witnesses final))
    ready : ReadyRun p src w start (State.inner-witnesses final) (IrSource.instructions src) final []

typed-honest-run : ComputeTypes → ∀ src p final → Producer src
  → (accepted : preprocess src p ≡ just final)
  → ForwardDomains (AcceptedRun.trace (preprocess-inversion {src} {p} accepted))
  → HonestRun src p final accepted
typed-honest-run operations src p final producer accepted domains
  with infer-success src producer
... | Γ , _ , inputs , instructions = record
  { inputs-agree = agreed
  ; encoded-inputs = trans (encode-installed-inputs (honest-witness p final) (InitialStore.values initial)
                              (InitialStore.installed initial) matches) (InitialStore.raw initial)
  ; initialized = initialized
  ; ready = ready-from-preprocess src p final (honest-witness p final) accepted (supported-trace replay domains) }
  where
  accepted-run = preprocess-inversion {src} {p} accepted
  start = AcceptedRun.initial accepted-run
  initial = initial-store src p (AcceptedRun.initialized accepted-run) inputs
  replay = trace-store operations (AcceptedRun.trace accepted-run) Γ
    (WriteFrame.typed-after (InitialStore.frame initial)) instructions
  agreed = initial-agreement src p start final Γ initial (trace-extends replay)
  matches = proj₂ (proj₂ agreed)
  initialized = init-forward-decoded src p (honest-witness p final) (InitialStore.values initial)
    (init-decodes src p (AcceptedRun.initialized accepted-run))
    (InitialStore.installed initial) matches refl refl
    (AcceptedRun.initialized accepted-run)

forward-with-typed-compute : ComputeTypes → ∀ src p final
  → PreparationForward → Producer src
  → (accepted : preprocess src p ≡ just final)
  → ForwardDomains (AcceptedRun.trace (preprocess-inversion {src} {p} accepted))
  → satisfies src (honest-witness p final) (view final [])
forward-with-typed-compute operations src p final preparation producer accepted domains =
  forward-using src p final preparation accepted inputs-agree initialized ready
  where open HonestRun (typed-honest-run operations src p final producer accepted domains)
