{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.TreeTrace (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.AccumulatorEffects ⋯ using (Prepared; Valid; prepared-step)
open import zkir-v4.AccumulatorObligations ⋯ using
  (PreparationsSatisfy; ValidConsumptions; obligations-or-bad-fold)
open import zkir-v4.AccumulatorObligations ⋯ public using
  (Occurs; at-head; in-tail; ConsumptionAt; fold-operand; exposed-value; Consumed; BadFold)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws)
open import zkir-v4.CircuitProperties ⋯ using (Trace; end; next; SatisfiedRun)
open import zkir-v4.Producer ⋯ using (Producer)
open import zkir-v4.RecursiveVerification ⋯ using (DirectLaws; module Active)
open import zkir-v4.Syntax ⋯ using (IrSource; prepare-verification)

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just)
open import Data.Product using (∃; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

-- The equalities refer to the preparation recovered from this successful step.
data ActivePreparationAt {src w} (key : List Byte) (fields : List Fr) (opening : Accumulator) {st st′} :
    ∀ i → stepᶜ src w st (lower i) ≡ just st′ → Set where
  active-preparation : ∀ {g hash ops pr out}
    {ok : stepᶜ src w st (prepare-proof g hash ops pr out) ≡ just st′} →
    let e = prepared-step src w st g hash ops pr out ok in
    Prepared.active e ≡ true →
    Prepared.key e ≡ key →
    Prepared.fields e ≡ fields →
    Prepared.opening e ≡ opening →
    ActivePreparationAt key fields opening (prepare-verification g hash ops pr out) ok

record ChildLink {src w st final is} (path : Trace src w st (map lower is) final)
                 (key : List Byte) (fields : List Fr) (carried : List Accumulator) : Set where
  field
    opening : Accumulator
    preparation : Occurs (ActivePreparationAt {src} {w} key fields opening) is path
    consumptions : All (Consumed is path) carried

record TraceValidity {src w st final is} (path : Trace src w st (map lower is) final) : Set where
  field
    openings : PreparationsSatisfy (λ e → Valid (Prepared.opening e)) is path
    consumption-valid : ValidConsumptions is path

trace-sound-or-bad-fold : ∀ src w final → Producer src →
  (run : SatisfiedRun src w final) → All Valid (CircuitState.accs final) →
  TraceValidity {is = IrSource.instructions src} (SatisfiedRun.path run) ⊎
  BadFold (IrSource.instructions src) (SatisfiedRun.path run)
trace-sound-or-bad-fold src w final producer run final-good
  with obligations-or-bad-fold src w final producer run final-good
... | inj₁ (openings , uses) = inj₁ record { openings = openings ; consumption-valid = uses }
... | inj₂ bad = inj₂ bad

record OpeningEvidence (key : List Byte) (fields : List Fr) (opening : Accumulator) : Set where
  field
    raw : List Byte
    parsed : key-well-formed key ≡ true
    prepared : prepare-circuit key fields raw true ≡ just opening
    valid : Valid opening

private
  actual-opening : ∀ {src w st final key fields opening} is
    {path : Trace src w st (map lower is) final} →
    PreparationsSatisfy (λ e → Valid (Prepared.opening e)) is path →
    Occurs (ActivePreparationAt {src} {w} key fields opening) is path →
    OpeningEvidence key fields opening
  actual-opening (prepare-verification g hash ops pr out ∷ is)
    {path = next {st = st} ok rest} (good , _) (at-head (active-preparation on refl refl refl)) =
    record
    { raw = Prepared.raw e
    ; parsed = Prepared.parsed e
    ; prepared = subst
        (λ flag → prepare-circuit (Prepared.key e) (Prepared.fields e) (Prepared.raw e) flag ≡
          just (Prepared.opening e))
        on (Prepared.prepared e)
    ; valid = good on
    }
    where
    e = prepared-step _ _ st g hash ops pr out ok
  actual-opening (i ∷ is) {path = next ok rest} (_ , later) (in-tail event) =
    actual-opening is later event

opening-evidence : ∀ {src w st final is key fields opening}
  {path : Trace src w st (map lower is) final} →
  TraceValidity {is = is} path →
  Occurs (ActivePreparationAt {src} {w} key fields opening) is path →
  OpeningEvidence key fields opening
opening-evidence {is = is} good = actual-opening is (TraceValidity.openings good)

recover-child : ∀ {Direct : List Byte → List Fr → List Byte → Set}
  {src w st final is key fields carried} {path : Trace src w st (map lower is) final} →
  PreparationLaws → DirectLaws Direct key fields → TraceValidity {is = is} path →
  ChildLink {is = is} path key fields carried →
  (∃ λ raw → Direct key fields raw) × All Valid carried
recover-child chip laws good link with opening-evidence good (ChildLink.preparation link)
... | e = Active.circuit-to-direct laws chip (OpeningEvidence.parsed e)
            (OpeningEvidence.raw e) (ChildLink.opening link)
            (OpeningEvidence.prepared e) (OpeningEvidence.valid e) ,
          All.map (TraceValidity.consumption-valid good _) (ChildLink.consumptions link)
