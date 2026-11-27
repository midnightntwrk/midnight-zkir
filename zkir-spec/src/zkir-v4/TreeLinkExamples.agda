{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.TreeLinkExamples (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.AccumulatorEffects ⋯ using
  (Prepared; prepared-step; Folded; fold-step; Exposed; expose-step)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitProperties ⋯ using (Trace; next; end)
open import zkir-v4.Operations ⋯ using (resolve-acc)
open import zkir-v4.Protocol ⋯ using (instance-fields)
open import zkir-v4.ReverseShape ⋯ using (immediate-true)
open import zkir-v4.Syntax ⋯ using (Operand; var; imm; prepare-verification; accumulate; verify-accumulator)
open import zkir-v4.TreeTrace ⋯ using
  (ChildLink; Occurs; ActivePreparationAt; active-preparation; at-head; in-tail; fold-operand; exposed-value)

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All as All using ()
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import Relation.Nullary using (¬_)

private
  fold-ops : List Operand
  fold-ops = var "%left-carried" ∷ var "%left-opening" ∷ var "%right-opening" ∷ []

  active : ∀ {src st hash ops pr out st′} (e : Prepared src st (imm 1ᶠ) hash ops pr out st′) →
    Prepared.active e ≡ true
  active {st = st} e = just-injective (trans (sym (Prepared.guard-ok e)) (immediate-true st))

-- The two children carry one accumulator each.  One is folded with both
-- openings, and the other is exposed directly.
module TwoChildren {src w start after-left after-right after-fold after-expose final}
  {left-hash right-hash : List Byte} {left-ops right-ops : List Operand}
  (left-ok : stepᶜ src w start
    (prepare-proof (imm 1ᶠ) left-hash left-ops "%left-proof" "%left-opening") ≡ just after-left)
  (right-ok : stepᶜ src w after-left
    (prepare-proof (imm 1ᶠ) right-hash right-ops "%right-proof" "%right-opening") ≡ just after-right)
  (fold-ok : stepᶜ src w after-right (fold-accs fold-ops "%folded") ≡ just after-fold)
  (expose-ok : stepᶜ src w after-fold (publish-acc (var "%right-carried")) ≡ just after-expose)
  (expose-fold-ok : stepᶜ src w after-expose (publish-acc (var "%folded")) ≡ just final) where

  private
    code =
      prepare-verification (imm 1ᶠ) left-hash left-ops "%left-proof" "%left-opening" ∷
      prepare-verification (imm 1ᶠ) right-hash right-ops "%right-proof" "%right-opening" ∷
      accumulate fold-ops "%folded" ∷
      verify-accumulator (var "%right-carried") ∷
      verify-accumulator (var "%folded") ∷ []

    left = prepared-step src w start (imm 1ᶠ) left-hash left-ops "%left-proof" "%left-opening" left-ok
    right = prepared-step src w after-left (imm 1ᶠ) right-hash right-ops "%right-proof" "%right-opening" right-ok
    fold = fold-step src w after-right fold-ops "%folded" fold-ok
    exposure = expose-step src w after-fold (var "%right-carried") expose-ok
    carried-right = Exposed.value exposure

  path : Trace src w start (map lower code) final
  path = next left-ok (next right-ok (next fold-ok (next expose-ok (next expose-fold-ok end))))

  links : ∀ carried-left left-stmt right-stmt →
    Prepared.fields left ≡ instance-fields (carried-left ∷ []) left-stmt →
    Prepared.fields right ≡ instance-fields (carried-right ∷ []) right-stmt →
    Folded.inputs fold ≡ carried-left ∷ Prepared.opening left ∷ Prepared.opening right ∷ [] →
    ChildLink {is = code} path (Prepared.key left)
      (instance-fields (carried-left ∷ []) left-stmt) (carried-left ∷ []) ×
    ChildLink {is = code} path (Prepared.key right)
      (instance-fields (carried-right ∷ []) right-stmt) (carried-right ∷ [])
  links carried-left _ _ left-fields right-fields inputs =
    record
      { opening = Prepared.opening left
      ; preparation = at-head (active-preparation (active left) refl left-fields refl)
      ; consumptions = in-tail (in-tail (at-head (fold-operand member))) All.∷ All.[]
      } ,
    record
      { opening = Prepared.opening right
      ; preparation = in-tail (at-head (active-preparation (active right) refl right-fields refl))
      ; consumptions = in-tail (in-tail (in-tail (at-head (exposed-value refl)))) All.∷ All.[]
      }
    where
    member : carried-left ∈ Folded.inputs fold
    member = subst (carried-left ∈_) (sym inputs) (here refl)

-- The parent's opening is discharged.  The child's distinct carry has no use.
module DischargeOpening {src w start after final} {hash : List Byte} {ops : List Operand}
  (ok : stepᶜ src w start (prepare-proof (imm 1ᶠ) hash ops "%proof" "%opening") ≡ just after)
  (expose-ok : stepᶜ src w after (publish-acc (var "%opening")) ≡ just final) where

  private
    code = prepare-verification (imm 1ᶠ) hash ops "%proof" "%opening" ∷
           verify-accumulator (var "%opening") ∷ []

    prep = prepared-step src w start (imm 1ᶠ) hash ops "%proof" "%opening" ok
    exposure = expose-step src w after (var "%opening") expose-ok

    resolve-opening : resolve-acc (CircuitState.mem after) (var "%opening") ≡ just (Prepared.opening prep)
    resolve-opening rewrite Prepared.stored prep = refl

    exposed-opening : Exposed.value exposure ≡ Prepared.opening prep
    exposed-opening = just-injective (trans (sym (Exposed.resolved exposure)) resolve-opening)

  path : Trace src w start (map lower code) final
  path = next ok (next expose-ok end)

  opening-prepared : ∀ a stmt →
    Prepared.fields prep ≡ instance-fields (a ∷ []) stmt →
    Occurs (ActivePreparationAt (Prepared.key prep) (instance-fields (a ∷ []) stmt)
      (Prepared.opening prep)) code path
  opening-prepared a stmt fields = at-head (active-preparation (active prep) refl fields refl)

  no-carried-link : ∀ key fields a rest →
    ¬ (a ≡ Prepared.opening prep) → ¬ ChildLink {is = code} path key fields (a ∷ rest)
  no-carried-link _ _ _ _ distinct link with ChildLink.consumptions link
  ... | at-head () All.∷ _
  ... | in-tail (at-head (exposed-value eq)) All.∷ _ = distinct (trans (sym eq) exposed-opening)
  ... | in-tail (in-tail ()) All.∷ _
