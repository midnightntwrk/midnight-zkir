{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.StatementSoundness (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Syntax ⋯ using (IrSource)
open import zkir-v4.Semantics ⋯ using (State; preprocess)
open import zkir-v4.SemanticsProperties ⋯ using (preprocess-exposure)
open import zkir-v4.Validation ⋯ using (validate)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitProperties ⋯ using (satisfying-public-inputs)
open import zkir-v4.CircuitEffects ⋯ using (PreparationLaws; PreparationBackward; preparation-backward)
open import zkir-v4.CircuitInputs ⋯ using (ValidDeclarations)
open import zkir-v4.CircuitExtraction ⋯ using (Fragment; extract)
open import zkir-v4.CircuitReplay ⋯ using (ReplayTrace; extraction-complete-using)
open import zkir-v4.EncodingProperties ⋯ using (EncodingLaws)
open import zkir-v4.Protocol ⋯
open import zkir-v4.ProtocolProperties ⋯ using (instance-inj)
open import Data.Bool using (true)
open import Data.List using (List; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just)
open import Data.Product using (∃; _,_; _×_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans; sym)

record WitnessShape (src : IrSource) (w : CircuitWitness) (target : CircuitState) : Set where
  field
    start : CircuitState
    streams : Fragment
    initialized : initᶜ src w ≡ just start
    path : ReplayTrace src w start (IrSource.instructions src) streams target
    input-stability : IrSource.do-communications-commitment src ≡ true →
        encode-inputs (CircuitState.mem target) (IrSource.inputs src) ≡
        encode-inputs (CircuitState.mem start) (IrSource.inputs src)

-- Circuit knowledge soundness recovers some satisfying witness.  Any
-- extra guard and assignment conditions required of that witness are
-- visible in the hypothesis.  For example synthesis of a transcript
-- read does not itself enforce its off-circuit guard.
module ForKey (src : IrSource) (OuterOK : List Byte → List Fr → Set) where
  open Verification OuterOK hiding (sound)

  ExtractsShapedWitness : Set
  ExtractsShapedWitness = ∀ raw pi → OuterOK raw pi →
    ∃ λ w → ∃ λ st → satisfies src w st × CircuitWitness.full-pis w ≡ pi × WitnessShape src w st

  sound-using : EncodingLaws → PreparationBackward
        → validate src ≡ true → ValidDeclarations (IrSource.inputs src)
        → ExtractsShapedWitness → ∀ {pr stmt}
        → Accepts (exposures (IrSource.instructions src)) pr stmt
        → (∃ λ w → ∃ λ p → ∃ λ final → extract src w ≡ just p × preprocess src p ≡ just final
                  × State.exposed final ≡ Proof.carried pr × State.pis final ≡ stmt)
          × All PairingOK (Proof.carried pr)
  sound-using codecs prepare valid decls backend {pr} {stmt} accepted
    with backend _ _ (Accepts.outer-valid accepted)
  ... | w , st , sat , bound , shape
    with extraction-complete-using codecs prepare src w _ st _ valid decls
           (WitnessShape.initialized shape) sat (WitnessShape.path shape) (WitnessShape.input-stability shape)
  ...   | p , final , extracted , ran , matches =
    (w , p , final , extracted , ran , instance-inj codecs as carried count fields) , Accepts.pairings accepted
    where
    as = State.exposed final
    carried = Proof.carried pr
    count : length as ≡ length carried
    count = trans (proj₂ (preprocess-exposure {src} {p} ran)) (sym (Accepts.count-matches accepted))
    fields : instance-fields as (State.pis final) ≡ instance-fields carried stmt
    fields = trans (cong full-public-inputsᶜ matches)
              (trans (satisfying-public-inputs {src} {w} {st} sat) bound)

  sound : EncodingLaws → PreparationLaws
        → validate src ≡ true → ValidDeclarations (IrSource.inputs src)
        → ExtractsShapedWitness → ∀ {pr stmt}
        → Accepts (exposures (IrSource.instructions src)) pr stmt
        → (∃ λ w → ∃ λ p → ∃ λ final → extract src w ≡ just p × preprocess src p ≡ just final
                  × State.exposed final ≡ Proof.carried pr × State.pis final ≡ stmt)
          × All PairingOK (Proof.carried pr)
  sound codecs prepare = sound-using codecs (preparation-backward prepare)
