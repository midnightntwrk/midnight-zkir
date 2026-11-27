{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.CircuitDiagnostics (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.Types ⋯
open import zkir-v4.Syntax ⋯
open import zkir-v4.Operations ⋯ hiding (write)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitBridge ⋯ using (WriteAgreement; write-agreed; write-backward)
open import zkir-v4.Validation ⋯ using (resolve-vk; validate)
open import zkir-v4.Producer ⋯ using (Producer)
open import zkir-v4.CircuitBindingNames ⋯ using (output-names; producer-names-unique)
open import zkir-v4.CircuitWriteNames ⋯ using (compute-names; bounded-names)
import zkir-v4.ProducerCorrespondence ⋯ as Checked

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.List.Relation.Unary.All as All using (All)
  renaming ([] to all[]; _∷_ to _all∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Membership.DecPropositional as DecMembership
import Data.String.Properties as Strings
open DecMembership Strings._≟_ using (_∈?_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_; fromMaybe)
open import Data.Nat using (_^_; _<?_; _≤?_)
open import Data.Product using (_×_; _,_; ∃; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

private
  infix 4 _⊑_
  _⊑_ : ∀ {A : Set} → Maybe A → Maybe A → Set
  a ⊑ b = ∀ {v} → a ≡ just v → b ≡ just v

  bind-compare : ∀ {A B : Set} (m : Maybe A) (f g : A → Maybe B)
    → (∀ a → m ≡ just a → f a ⊑ g a) → (m >>= f) ⊑ (m >>= g)
  bind-compare nothing f g local ()
  bind-compare (just a) f g local ok = local a refl ok

  equal-bind : ∀ {A B : Set} (m n : Maybe A) (f g : A → Maybe B)
    → m ≡ n → (∀ a → n ≡ just a → f a ⊑ g a) → (m >>= f) ⊑ (n >>= g)
  equal-bind m .m f g refl local = bind-compare m f g local

  same-bind : ∀ {A B : Set} (m : Maybe A) {f g : A → Maybe B}
    → (∀ a → f a ⊑ g a) → (m >>= f) ⊑ (m >>= g)
  same-bind m local = bind-compare m _ _ (λ a _ → local a)

  continue : ∀ {A B : Set} {m n : Maybe A} {f g : A → Maybe B}
    → m ⊑ n → (∀ a → f a ⊑ g a) → (m >>= f) ⊑ (n >>= g)
  continue {m = nothing} head tail ()
  continue {m = just a} head tail ok rewrite head refl = tail a ok

  guarded : ∀ {P A : Set} (dec : Dec P) {m n : Maybe A}
    → m ⊑ n → guardD dec m ⊑ guardD dec n
  guarded (no _) local ()
  guarded (yes _) local = local

  if-success : ∀ {A : Set} (b : Bool) {m n : Maybe A}
    → m ⊑ n → (if b then m else nothing) ⊑ (if b then n else nothing)
  if-success false local ()
  if-success true local = local

  compare-writes : ∀ checked checked′ w w′ st ws
    → WriteAgreement checked′ w′ ws → write checked w st ws ⊑ write checked′ w′ st ws
  compare-writes checked checked′ w w′ st ws agree ok =
    trans (write-agreed checked′ w′ st ws agree)
          (cong just (sym (write-backward checked w st ws ok)))

  compare-computed : ∀ d d′ checked w w′ st ws
    → WriteAgreement (if d′ then checked else false) w′ ws
    → write (if d then checked else false) w st ws ⊑ write (if d′ then checked else false) w′ st ws
  compare-computed d d′ checked = compare-writes (if d then checked else false) (if d′ then checked else false)

  reads-from : Constraint → Identifier → Set
  reads-from (witness-cell _ id) x = id ≡ x
  reads-from _ _ = ⊥

  SingleWrite : Identifier → List (Identifier × IrValue) → Set
  SingleWrite out ws = ∃ λ v → ws ≡ (out , v) ∷ []

  computed-by : Mem → Constraint → List (Identifier × IrValue) → Set
  computed-by m (shared i) ws = compute m i ≡ just ws
  computed-by m (bounded-bits _ i) ws = bounded-compute m i ≡ just ws
  computed-by _ (legacy-from-parts _ _ out) ws = SingleWrite out ws
  computed-by _ (chip-select _ _ _ out) ws = SingleWrite out ws
  computed-by _ (chip-eq _ _ (just out)) ws = SingleWrite out ws
  computed-by _ (chip-less-than _ _ _ out) ws = SingleWrite out ws
  computed-by _ (aligned-hash _ _ _ out) ws = SingleWrite out ws
  computed-by _ (prepare-proof _ _ _ _ out) ws = SingleWrite out ws
  computed-by _ (fold-accs _ out) ws = SingleWrite out ws
  computed-by _ _ _ = ⊥

  step-compare : ∀ diagnostics diagnostics′ src w w′ st c
    → (∀ id → reads-from c id → CircuitWitness.assign w id ≡ CircuitWitness.assign w′ id)
    → (∀ checked ws → computed-by (CircuitState.mem st) c ws →
         WriteAgreement (if diagnostics′ then checked else false) w′ ws)
    → step-with diagnostics src w st c ⊑ step-with diagnostics′ src w′ st c
  step-compare d d′ src w w′ st (shared i) reads writes =
    bind-compare (compute (CircuitState.mem st) i) _ _ λ ws computed →
      compare-computed d d′ (check-shared-writes i) w w′ st ws (writes (check-shared-writes i) ws computed)
  step-compare d d′ src w w′ st (bounded-bits bits i) reads writes =
    guarded (bits ≤? FR-BITS)
      (bind-compare (bounded-compute (CircuitState.mem st) i) _ _ λ ws computed →
        compare-computed d d′ true w w′ st ws (writes true ws computed))
  step-compare d d′ src w w′ st (legacy-from-parts lo hi out) reads writes =
    same-bind (resolveᶠ m hi) λ high →
    same-bind (resolve m lo) λ low →
    same-bind (bytes32-from-parts low (val-native high)) λ bs →
      compare-computed d d′ false w w′ st _ (writes false _ (val-bytes bs , refl))
    where m = CircuitState.mem st
  step-compare d d′ src w w′ st (non-zero _) reads writes ok = ok
  step-compare d d′ src w w′ st (chip-select bit a b out) reads writes =
    same-bind (resolve𝔹 m bit) λ g →
    same-bind (resolve m a) λ x →
    same-bind (resolve m b) λ y →
    guarded (typeof x ≟T typeof y)
      (if-success (select-supported (typeof x))
        (compare-computed d d′ true w w′ st _ (writes true _ ((if g then x else y) , refl))))
    where m = CircuitState.mem st
  step-compare d d′ src w w′ st (chip-eq _ _ nothing) reads writes ok = ok
  step-compare d d′ src w w′ st (chip-eq a b (just out)) reads writes =
    same-bind (chip-equality (CircuitState.mem st) a b) λ g →
      compare-computed d d′ true w w′ st _ (writes true _ (val-native (χ g) , refl))
  step-compare d d′ src w w′ st (chip-less-than a b bits out) reads writes =
    same-bind (resolveᶠ m a) λ x →
    same-bind (resolveᶠ m b) λ y →
    guarded (valFr x <? 2 ^ even4 bits) (guarded (valFr y <? 2 ^ even4 bits) (compare (valFr x <? valFr y)))
    where
    m = CircuitState.mem st
    result : Bool → CircuitWitness → IrValue → Maybe CircuitState
    result diagnostics witness value =
      write (if diagnostics then true else false) witness st ((out , value) ∷ [])
    compare : ∀ {P : Set} (decision : Dec P) →
      comparison-result (result d w) decision ⊑ comparison-result (result d′ w′) decision
    compare (yes _) = compare-computed d d′ true w w′ st _ (writes true _ (val-native 1ᶠ , refl))
    compare (no _) = compare-computed d d′ true w w′ st _ (writes true _ (val-native 0ᶠ , refl))
  step-compare d d′ src w w′ st (aligned-hash kind a ops out) reads writes =
    same-bind (resolve-all-Fr (CircuitState.mem st) ops) λ xs →
    same-bind (digestᶜ kind a xs) λ bs →
      compare-computed d d′ true w w′ st _ (writes true _ (val-bytes bs , refl))
  step-compare d d′ src w w′ st (witness-cell t id) reads writes =
    equal-bind (CircuitWitness.assign w id >>= assign-value t)
      (CircuitWitness.assign w′ id >>= assign-value t) _ _
      (cong (_>>= assign-value t) (reads id refl)) local
    where
    read-agreement : ∀ flag v → CircuitWitness.assign w′ id ≡ just v
      → WriteAgreement flag w′ ((id , v) ∷ [])
    read-agreement false _ _ = tt
    read-agreement true _ found = inj₂ found , tt
    assigned : ∀ m v → (m >>= assign-value t) ≡ just v → m ≡ just v
    assigned nothing v ()
    assigned (just cell) v ok with typeof cell ≟T t
    ... | no _ with () ← ok
    assigned (just cell) v ok | yes _ = ok
    local : ∀ v → (CircuitWitness.assign w′ id >>= assign-value t) ≡ just v →
      write d w st ((id , v) ∷ []) ⊑ write d′ w′ st ((id , v) ∷ [])
    local v found = compare-writes d d′ w w′ st ((id , v) ∷ [])
      (read-agreement d′ v (assigned (CircuitWitness.assign w′ id) v found))
  step-compare d d′ src w w′ st (publish-impact _ _) reads writes ok = ok
  step-compare d d′ src w w′ st (record-output _) reads writes ok = ok
  step-compare d d′ src w w′ st (bind-proof _) reads writes ok = ok
  step-compare d d′ src w w′ st (prepare-proof g h ops id out) reads writes =
    same-bind (resolve𝔹 m g) λ active →
    same-bind (resolve-all-Fr m ops) λ instance-values →
    same-bind (CircuitState.proofs st id) λ bytes →
    same-bind (resolve-vk h (IrSource.inner-vks src)) λ vk →
    if-success (key-well-formed vk)
      (same-bind (prepare-circuit vk instance-values bytes active) λ acc →
        compare-computed d d′ true w w′ st _ (writes true _ (val-accumulator acc , refl)))
    where m = CircuitState.mem st
  step-compare d d′ src w w′ st (fold-accs ops out) reads writes =
    same-bind (resolve-accs (CircuitState.mem st) ops) λ where
      accs@(_ ∷ _ ∷ _) →
        same-bind (fold-accumulators accs) λ acc →
          compare-computed d d′ true w w′ st _ (writes true _ (val-accumulator acc , refl))
      [] → λ ()
      (_ ∷ []) → λ ()
  step-compare d d′ src w w′ st (publish-acc _) reads writes ok = ok

  compare-check : ∀ d d′ src w w′
    → initᶜ src w ≡ initᶜ src w′
    → (∀ st → run-with d src w st (map lower (IrSource.instructions src))
            ⊑ run-with d′ src w′ st (map lower (IrSource.instructions src)))
    → (∀ st → finishᶜ src w st ≡ finishᶜ src w′ st)
    → check-with d src w ⊑ check-with d′ src w′
  compare-check d d′ src w w′ initial walk finish with validate src
  ... | false = λ ()
  ... | true =
    equal-bind (initᶜ src w) (initᶜ src w′) _ _ initial λ st _ →
      continue (walk st) λ final ok → trans (sym (finish final)) ok

  unchecked-run : ∀ src w st cs → runᶜ src w st cs ⊑ run-with false src w st cs
  unchecked-run src w st [] ok = ok
  unchecked-run src w st (c ∷ cs) = continue
    (step-compare true false src w w st c (λ _ _ → refl) (λ _ _ _ → tt))
    (λ next → unchecked-run src w next cs)

checked→constraints : ∀ {src w st} → satisfies src w st → satisfies-constraints src w st
checked→constraints {src} {w} =
  compare-check true false src w w refl
    (λ st → unchecked-run src w st (map lower (IrSource.instructions src))) (λ _ → refl)

private
  transcript-names : Constraint → List Identifier
  transcript-names (witness-cell _ id) = id ∷ []
  transcript-names _ = []

  computed-names : Constraint → List Identifier
  computed-names (shared i) = output-names i
  computed-names (bounded-bits _ i) = output-names i
  computed-names (legacy-from-parts _ _ out) = out ∷ []
  computed-names (chip-select _ _ _ out) = out ∷ []
  computed-names (chip-eq _ _ (just out)) = out ∷ []
  computed-names (chip-less-than _ _ _ out) = out ∷ []
  computed-names (aligned-hash _ _ _ out) = out ∷ []
  computed-names (prepare-proof _ _ _ _ out) = out ∷ []
  computed-names (fold-accs _ out) = out ∷ []
  computed-names _ = []

  cell-names : Constraint → List Identifier
  cell-names c = transcript-names c ++ computed-names c

  lowered-names : ∀ i → cell-names (lower i) ≡ output-names i
  lowered-names (encode _ os) = refl
  lowered-names (assert _) = refl
  lowered-names (cond-select _ _ _ o) = refl
  lowered-names (constrain-bits _ _) = refl
  lowered-names (constrain-eq _ _) = refl
  lowered-names (constrain-to-boolean _) = refl
  lowered-names (copy _ o) = refl
  lowered-names (impact _ _) = refl
  lowered-names (ec-mul _ _ o) = refl
  lowered-names (ec-mul-generator _ o) = refl
  lowered-names (hash-to-curve _ o) = refl
  lowered-names (into-coordinates _ (x , y)) = refl
  lowered-names (from-coordinates (_ , _) o) = refl
  lowered-names (into-bytes32 _ o) = refl
  lowered-names (from-bytes32 _ _ o) = refl
  lowered-names (reverse-bytes _ o) = refl
  lowered-names (bytes32-into-low-high _ (lo , hi)) = refl
  lowered-names (bytes32-from-low-high (_ , _) _) = refl
  lowered-names (div-mod-power-of-two _ _ os) = refl
  lowered-names (reconstitute-field _ _ _ o) = refl
  lowered-names (transient-hash _ o) = refl
  lowered-names (persistent-hash _ _ o) = refl
  lowered-names (keccak256 _ _ o) = refl
  lowered-names (test-eq _ _ o) = refl
  lowered-names (add _ _ o) = refl
  lowered-names (mul _ _ o) = refl
  lowered-names (neg _ o) = refl
  lowered-names (inv _ o) = refl
  lowered-names (not _ o) = refl
  lowered-names (less-than _ _ _ o) = refl
  lowered-names (jubjub-scalar-from-native _ o) = refl
  lowered-names (public-input _ _ o) = refl
  lowered-names (private-input _ _ o) = refl
  lowered-names (circuit-output _) = refl
  lowered-names (slice _ _ _ o) = refl
  lowered-names (nth _ _ o) = refl
  lowered-names (concat _ o) = refl
  lowered-names (reverse _ o) = refl
  lowered-names (load-constant _ _ o) = refl
  lowered-names (sha512 _ _ o) = refl
  lowered-names (and _ o) = refl
  lowered-names (or _ o) = refl
  lowered-names (xor _ o) = refl
  lowered-names (to-bytes _ o) = refl
  lowered-names (from-bytes _ _ o) = refl
  lowered-names (bytes-into-natives _ os) = refl
  lowered-names (bytes-from-natives _ _ o) = refl
  lowered-names (inner-proof _ _) = refl
  lowered-names (prepare-verification _ _ _ _ o) = refl
  lowered-names (accumulate _ o) = refl
  lowered-names (verify-accumulator _) = refl

  code-names : ∀ is → concatMap cell-names (map lower is) ≡ concatMap output-names is
  code-names [] = refl
  code-names (i ∷ is) rewrite lowered-names i | code-names is = refl

  read-member : ∀ c id → reads-from c id → id ∈ transcript-names c
  read-member (witness-cell _ id) .id refl = here refl
  read-member (shared _) _ ()
  read-member (bounded-bits _ _) _ ()
  read-member (legacy-from-parts _ _ _) _ ()
  read-member (non-zero _) _ ()
  read-member (chip-select _ _ _ _) _ ()
  read-member (chip-eq _ _ nothing) _ ()
  read-member (chip-eq _ _ (just _)) _ ()
  read-member (chip-less-than _ _ _ _) _ ()
  read-member (aligned-hash _ _ _ _) _ ()
  read-member (publish-impact _ _) _ ()
  read-member (record-output _) _ ()
  read-member (bind-proof _) _ ()
  read-member (prepare-proof _ _ _ _ _) _ ()
  read-member (fold-accs _ _) _ ()
  read-member (publish-acc _) _ ()

  write-members : ∀ m c ws → computed-by m c ws → map proj₁ ws ≡ computed-names c
  write-members m (shared i) ws = compute-names m i
  write-members m (bounded-bits _ i) ws = bounded-names m i
  write-members m (legacy-from-parts _ _ _) ._ (_ , refl) = refl
  write-members m (non-zero _) ws ()
  write-members m (chip-select _ _ _ _) ._ (_ , refl) = refl
  write-members m (chip-eq _ _ nothing) ws ()
  write-members m (chip-eq _ _ (just _)) ._ (_ , refl) = refl
  write-members m (chip-less-than _ _ _ _) ._ (_ , refl) = refl
  write-members m (aligned-hash _ _ _ _) ._ (_ , refl) = refl
  write-members m (witness-cell _ _) ws ()
  write-members m (publish-impact _ _) ws ()
  write-members m (record-output _) ws ()
  write-members m (bind-proof _) ws ()
  write-members m (prepare-proof _ _ _ _ _) ._ (_ , refl) = refl
  write-members m (fold-accs _ _) ._ (_ , refl) = refl
  write-members m (publish-acc _) ws ()

  unique-tail : ∀ (before after : List Identifier) → Unique (before ++ after) → Unique after
  unique-tail [] after unique = unique
  unique-tail (_ ∷ before) after (_ ∷ unique) = unique-tail before after unique

  unique-cross : ∀ {x} (before after : List Identifier) → Unique (before ++ after)
    → x ∈ before → x ∈ after → ⊥
  unique-cross [] after unique ()
  unique-cross (id ∷ before) after (fresh ∷ unique) (here refl) later =
    All.lookup fresh (∈-++⁺ʳ before later) refl
  unique-cross (_ ∷ before) after (_ ∷ unique) (there earlier) later =
    unique-cross before after unique earlier later

  subset-code : ∀ (names : Constraint → List Identifier) cs {id}
    → (∀ c → id ∈ names c → id ∈ cell-names c)
    → id ∈ concatMap names cs → id ∈ concatMap cell-names cs
  subset-code names [] embed ()
  subset-code names (c ∷ cs) embed found with ∈-++⁻ (names c) found
  ... | inj₁ head = ∈-++⁺ˡ (embed c head)
  ... | inj₂ tail = ∈-++⁺ʳ (cell-names c) (subset-code names cs embed tail)

  computed-subset : ∀ cs {id} → id ∈ concatMap computed-names cs → id ∈ concatMap cell-names cs
  computed-subset cs = subset-code computed-names cs (λ c → ∈-++⁺ʳ (transcript-names c))

  transcript-subset : ∀ cs {id} → id ∈ concatMap transcript-names cs → id ∈ concatMap cell-names cs
  transcript-subset cs = subset-code transcript-names cs (λ _ → ∈-++⁺ˡ)

  head-disjoint : ∀ c rest {id} → Unique (cell-names c ++ rest)
    → id ∈ transcript-names c → id ∈ computed-names c → ⊥
  head-disjoint c rest unique read computed =
    unique-cross (transcript-names c) (computed-names c ++ rest) (reassociate unique)
      read (∈-++⁺ˡ computed)
    where
    open import Data.List.Properties using (++-assoc)
    reassociate : Unique (cell-names c ++ rest) →
      Unique (transcript-names c ++ (computed-names c ++ rest))
    reassociate = subst Unique (++-assoc (transcript-names c) (computed-names c) rest)

  code-disjoint : ∀ cs {id} → Unique (concatMap cell-names cs)
    → id ∈ concatMap computed-names cs → id ∈ concatMap transcript-names cs → ⊥
  code-disjoint [] unique ()
  code-disjoint (c ∷ cs) unique computed read
    with ∈-++⁻ (computed-names c) computed | ∈-++⁻ (transcript-names c) read
  ... | inj₁ local-computed | inj₁ local-read =
    head-disjoint c (concatMap cell-names cs) unique local-read local-computed
  ... | inj₁ local-computed | inj₂ later-read =
    unique-cross (cell-names c) (concatMap cell-names cs) unique
      (∈-++⁺ʳ (transcript-names c) local-computed) (transcript-subset cs later-read)
  ... | inj₂ later-computed | inj₁ local-read =
    unique-cross (cell-names c) (concatMap cell-names cs) unique
      (∈-++⁺ˡ local-read) (computed-subset cs later-computed)
  ... | inj₂ later-computed | inj₂ later-read =
    code-disjoint cs (unique-tail (cell-names c) (concatMap cell-names cs) unique) later-computed later-read

  declared-names : IrSource → List Identifier
  declared-names src = map TypedIdentifier.name (IrSource.inputs src)

  constraints : IrSource → List Constraint
  constraints src = map lower (IrSource.instructions src)

  witnessed-names : IrSource → List Identifier
  witnessed-names src = declared-names src ++ concatMap transcript-names (constraints src)

  writes-disjoint : ∀ src → Producer src → ∀ {id}
    → id ∈ concatMap computed-names (constraints src) → id ∉ witnessed-names src
  writes-disjoint src producer computed read with ∈-++⁻ (declared-names src) read
  ... | inj₁ declared = unique-cross (declared-names src) (concatMap cell-names (constraints src))
                          unique declared (computed-subset (constraints src) computed)
    where
    unique = subst (λ names → Unique (declared-names src ++ names))
      (sym (code-names (IrSource.instructions src))) (producer-names-unique src producer)
  ... | inj₂ transcript = code-disjoint (constraints src)
      (unique-tail (declared-names src) (concatMap cell-names (constraints src)) unique) computed transcript
    where
    unique = subst (λ names → Unique (declared-names src ++ names))
      (sym (code-names (IrSource.instructions src))) (producer-names-unique src producer)

-- Declared and transcript cells are the only witness-memory inputs.
-- Binding, commitments, proof bytes and the full public instance survive
-- the restriction because they are separate fields of the witness.
normalize-witness : IrSource → CircuitWitness → CircuitWitness
normalize-witness src w = record w { assign = retain }
  where
  retain : Mem
  retain id with id ∈? witnessed-names src
  ... | yes _ = CircuitWitness.assign w id
  ... | no _ = nothing

private
  retained : ∀ src w id → id ∈ witnessed-names src
    → CircuitWitness.assign w id ≡ CircuitWitness.assign (normalize-witness src w) id
  retained src w id legal with id ∈? witnessed-names src
  ... | yes _ = refl
  ... | no absent = ⊥-elim (absent legal)

  erased : ∀ src w id → id ∉ witnessed-names src
    → CircuitWitness.assign (normalize-witness src w) id ≡ nothing
  erased src w id absent with id ∈? witnessed-names src
  ... | yes legal = ⊥-elim (absent legal)
  ... | no _ = refl

  declare-compare : ∀ w w′ m ds
    → (∀ id → id ∈ map TypedIdentifier.name ds → CircuitWitness.assign w id ≡ CircuitWitness.assign w′ id)
    → declare w m ds ≡ declare w′ m ds
  declare-compare w w′ m [] agree = refl
  declare-compare w w′ m ((id ⦂ t) ∷ ds) agree
    rewrite cong (fromMaybe (val-native 0ᶠ)) (agree id (here refl))
    with assign-value t (declared-value w′ id)
  ... | nothing = refl
  ... | just v = declare-compare w w′ (ins id v m) ds (λ next found → agree next (there found))
  normalized-initial : ∀ src w → initᶜ src w ≡ initᶜ src (normalize-witness src w)
  normalized-initial src w rewrite declare-compare w (normalize-witness src w) ∅ (IrSource.inputs src)
    (λ id found → retained src w id (∈-++⁺ˡ found)) = refl

  empty-agreement : ∀ checked w ws → All (λ pair → CircuitWitness.assign w (proj₁ pair) ≡ nothing) ws
    → WriteAgreement checked w ws
  empty-agreement false _ _ _ = tt
  empty-agreement true _ [] all[] = tt
  empty-agreement true w (_ ∷ ws) (head all∷ tail) = inj₁ head , empty-agreement true w ws tail

  normalized-run : ∀ src w → Producer src → ∀ st cs
    → (∀ id → id ∈ concatMap transcript-names cs → id ∈ concatMap transcript-names (constraints src))
    → (∀ id → id ∈ concatMap computed-names cs → id ∈ concatMap computed-names (constraints src))
    → run-with false src w st cs ⊑ runᶜ src (normalize-witness src w) st cs
  normalized-run src w producer st [] reads writes ok = ok
  normalized-run src w producer st (c ∷ cs) reads writes =
    continue (step-compare false true src w (normalize-witness src w) st c kept agreement)
      (λ next → normalized-run src w producer next cs
        (λ id found → reads id (∈-++⁺ʳ (transcript-names c) found))
        (λ id found → writes id (∈-++⁺ʳ (computed-names c) found)))
    where
    kept : ∀ id → reads-from c id → CircuitWitness.assign w id ≡
      CircuitWitness.assign (normalize-witness src w) id
    kept id read = retained src w id
      (∈-++⁺ʳ (declared-names src) (reads id (∈-++⁺ˡ (read-member c id read))))

    agreement : ∀ checked ws → computed-by (CircuitState.mem st) c ws →
      WriteAgreement checked (normalize-witness src w) ws
    agreement checked ws wrote = empty-agreement checked (normalize-witness src w) ws
      (All.tabulate λ {pair} found → erased src w (proj₁ pair)
        (writes-disjoint src producer
          (writes (proj₁ pair) (∈-++⁺ˡ
            (subst (proj₁ pair ∈_) (write-members (CircuitState.mem st) c ws wrote)
              (∈-map⁺ proj₁ found))))))

constraints→checked : ∀ {src w st} → Producer src → satisfies-constraints src w st
  → satisfies src (normalize-witness src w) st
constraints→checked {src} {w} producer =
  compare-check false true src w (normalize-witness src w) (normalized-initial src w)
    (λ st → normalized-run src w producer st (constraints src) (λ _ found → found) (λ _ found → found))
    (λ _ → refl)

AtInstance : (IrSource → CircuitWitness → CircuitState → Set) → IrSource → List Fr → Set
AtInstance relation src pi =
  ∃ λ w → ∃ λ st → relation src w st × CircuitWitness.full-pis w ≡ pi

private
  constraints-instance→checked : ∀ {src pi} → Producer src → AtInstance satisfies-constraints src pi
    → AtInstance satisfies src pi
  constraints-instance→checked {src} producer (w , st , sat , bound) =
    normalize-witness src w , st , constraints→checked {src = src} {w = w} {st = st} producer sat , bound

  checked-instance→constraints : ∀ {src pi} → AtInstance satisfies src pi
    → AtInstance satisfies-constraints src pi
  checked-instance→constraints {src} (w , st , sat , bound) =
    w , st , checked→constraints {src = src} {w = w} {st = st} sat , bound

public-instance-equivalence : ∀ src → Producer src → ∀ pi →
  AtInstance satisfies-constraints src pi ⇔ AtInstance satisfies src pi
public-instance-equivalence src producer pi =
  mk⇔ (constraints-instance→checked {src} {pi} producer) (checked-instance→constraints {src} {pi})

module ForKey (src : IrSource) (OuterOK : List Byte → List Fr → Set) where
  module Existing = Checked.ForKey src OuterOK

  ExtractsConstraintWitness : Set
  ExtractsConstraintWitness = ∀ raw pi → OuterOK raw pi →
    AtInstance satisfies-constraints src pi

  constraint-extraction→checked : Producer src → ExtractsConstraintWitness → Existing.ExtractsWitness
  constraint-extraction→checked producer backend raw pi accepted =
    constraints-instance→checked {src} {pi} producer (backend raw pi accepted)

  checked-extraction→constraints : Existing.ExtractsWitness → ExtractsConstraintWitness
  checked-extraction→constraints backend raw pi accepted =
    checked-instance→constraints {src} {pi} (backend raw pi accepted)
