{-# OPTIONS --safe #-}
open import zkir-v4.Assumptions

module zkir-v4.SegmentJoinObserve (⋯ : Assumptions) (open Assumptions ⋯) where

open import zkir-v4.AccumulatorEffects ⋯ using
  (Prepared; prepared-step; Folded; fold-step; Exposed; expose-step)
open import zkir-v4.Circuit ⋯
open import zkir-v4.CircuitProperties ⋯ using (SatisfiedRun; satisfying-run; Trace; next; end)
open import zkir-v4.Operations ⋯ using
  (Mem; ∅; ins; apply-writes; resolve-all-Fr; resolve-accs)
open import zkir-v4.Protocol ⋯ using (instance-fields)
open import zkir-v4.ReverseShape ⋯ using (immediate-true)
open import zkir-v4.SegmentEncoding ⋯ using
  (carry-writes; encoded-state; encode-carried; resolve-carried-fields; resolve-child;
   join-memory; published; publish-step)
open import zkir-v4.SegmentSource ⋯
open import zkir-v4.SequentialSource ⋯ using
  (declared-native; declared-accumulator; initial-state)
open import zkir-v4.Syntax ⋯
open import zkir-v4.Types ⋯ using (native; accumulator; val-native; val-accumulator)
open import zkir-v4.TreeTrace ⋯ using
  (ChildLink; ActivePreparationAt; active-preparation; at-head; in-tail; fold-operand)
open import zkir-v4.Validation ⋯ using (resolve-vk)

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (∷-injective; ∷-injectiveʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All as All using ()
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (_+_)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

private
  join-declared : ∀ w {mem} → declare w ∅ join-inputs ≡ just mem →
    ∃ λ c → ∃ λ a → ∃ λ m → ∃ λ b → ∃ λ lc → ∃ λ rc →
      mem ≡ join-memory c a m b lc rc
  join-declared w ok
    with c , rest-c ← declared-native w ∅ ctx
      (x ⦂ native ∷ mid ⦂ native ∷ z ⦂ native ∷ carry-id lhs ⦂ accumulator ∷ carry-id rhs ⦂ accumulator ∷ []) ok
    with a , rest-a ← declared-native w (ins ctx (val-native c) ∅) x
      (mid ⦂ native ∷ z ⦂ native ∷ carry-id lhs ⦂ accumulator ∷ carry-id rhs ⦂ accumulator ∷ []) rest-c
    with m , rest-m ← declared-native w (ins x (val-native a) (ins ctx (val-native c) ∅)) mid
      (z ⦂ native ∷ carry-id lhs ⦂ accumulator ∷ carry-id rhs ⦂ accumulator ∷ []) rest-a
    with b , rest-b ← declared-native w (ins mid (val-native m) (ins x (val-native a) (ins ctx (val-native c) ∅))) z
      (carry-id lhs ⦂ accumulator ∷ carry-id rhs ⦂ accumulator ∷ []) rest-m
    with lc , rest-lc ← declared-accumulator w
      (ins z (val-native b) (ins mid (val-native m) (ins x (val-native a) (ins ctx (val-native c) ∅))))
      (carry-id lhs) (carry-id rhs ⦂ accumulator ∷ []) rest-b
    with rc , done ← declared-accumulator w
      (ins (carry-id lhs) (val-accumulator lc)
        (ins z (val-native b) (ins mid (val-native m) (ins x (val-native a) (ins ctx (val-native c) ∅)))))
      (carry-id rhs) [] rest-lc =
    c , a , m , b , lc , rc , sym (just-injective done)

  initial-memory : ∀ w (declared : Maybe Mem) {start} →
    (declared >>= λ mem → just (initial-state w mem)) ≡ just start →
    ∃ λ mem → declared ≡ just mem × start ≡ initial-state w mem
  initial-memory w nothing ()
  initial-memory w (just mem) ok = mem , refl , sym (just-injective ok)

  JoinStart : CircuitWitness → CircuitState → Set
  JoinStart w start = ∃ λ c → ∃ λ a → ∃ λ m → ∃ λ b → ∃ λ lc → ∃ λ rc →
    start ≡ initial-state w (join-memory c a m b lc rc)

  from-inputs : ∀ w {start mem} → start ≡ initial-state w mem →
    (∃ λ c → ∃ λ a → ∃ λ m → ∃ λ b → ∃ λ lc → ∃ λ rc →
      mem ≡ join-memory c a m b lc rc) →
    JoinStart w start
  from-inputs w start-ok (c , a , m , b , lc , rc , mem-ok) =
    c , a , m , b , lc , rc , trans start-ok (cong (initial-state w) mem-ok)

  from-declared : ∀ w {start} →
    (∃ λ mem → declare w ∅ join-inputs ≡ just mem × start ≡ initial-state w mem) →
    JoinStart w start
  from-declared w (mem , declared , start-ok) = from-inputs w start-ok (join-declared w declared)

  join-start : ∀ keys l r w {start} → initᶜ (source keys (join l r)) w ≡ just start → JoinStart w start
  join-start keys l r w ok = from-declared w (initial-memory w (declare w ∅ join-inputs) ok)

  read-frame : ∀ src w st id {after} →
    stepᶜ src w st (bind-proof id) ≡ just after →
    (CircuitState.mem after ≡ CircuitState.mem st) ×
    (CircuitState.pis after ≡ CircuitState.pis st)
  read-frame src w st id ok with CircuitState.proof-rem st
  ... | [] with () ← ok
  read-frame src w st id ok | _ ∷ _ =
    cong CircuitState.mem (sym (just-injective ok)) ,
    cong CircuitState.pis (sym (just-injective ok))

  prepared-at : ∀ src w st key n s {after}
    (ok : stepᶜ src w st (prepare-proof (imm 1ᶠ) (key-digest key) (ops s n) (proof-id s) (opening-id s))
      ≡ just after) {fs} →
    resolve-vk (key-digest key) (IrSource.inner-vks src) ≡ just key →
    resolve-all-Fr (CircuitState.mem st) (ops s n) ≡ just fs →
    let e = prepared-step src w st (imm 1ᶠ) (key-digest key) (ops s n) (proof-id s) (opening-id s) ok
    in ActivePreparationAt {src} {w} key fs (Prepared.opening e)
      (prepare-verification (imm 1ᶠ) (key-digest key) (ops s n) (proof-id s) (opening-id s)) ok
  prepared-at src w st key n s ok pinned values =
    active-preparation (equal-just (Prepared.guard-ok e) (immediate-true st))
      (equal-just (Prepared.key-ok e) pinned) (equal-just (Prepared.instance-ok e) values) refl
    where
    e = prepared-step src w st (imm 1ᶠ) (key-digest key) (ops s n) (proof-id s) (opening-id s) ok

    equal-just : ∀ {A : Set} {f : Maybe A} {a b} → f ≡ just a → f ≡ just b → a ≡ b
    equal-just left right = just-injective (trans (sym left) right)

  record JoinObservation keys l r {w start final}
    (path : Trace (source keys (join l r)) w start
      (map lower (IrSource.instructions (source keys (join l r)))) final) : Set where
    private code = IrSource.instructions (source keys (join l r))
    field
      context begin midpoint finish : Fr
      left-carry right-carry : Accumulator
      statement : CircuitState.pis final ≡
        observed-fields (steps l + steps r) (CircuitWitness.binding-input w) context begin finish
      left-link : ChildLink {is = code} path (keys l)
        (instance-fields (left-carry ∷ []) (fields (steps l) context begin midpoint)) (left-carry ∷ [])
      right-link : ChildLink {is = code} path (keys r)
        (instance-fields (right-carry ∷ []) (fields (steps r) context midpoint finish)) (right-carry ∷ [])

  module AtJoin (keys : Shape → List Byte) (l r : Shape)
    (left-pinned : resolve-vk (key-digest (keys l)) (key-table (keys l) (keys r)) ≡ just (keys l))
    (right-pinned : resolve-vk (key-digest (keys r)) (key-table (keys l) (keys r)) ≡ just (keys r))
    (w : CircuitWitness) where

    src = source keys (join l r)
    code = IrSource.instructions src
    n = steps l + steps r

    walked : ∀ c a m b lc rc {final}
      (path : Trace src w (initial-state w (join-memory c a m b lc rc)) (map lower code) final) →
      JoinObservation keys l r path
    walked c a m b lc rc
      (next {st = start} publish-ok (next {st = s₁} left-encoded
      (next {st = s₂} left-read (next {st = s₃} left-prepared
      (next {st = s₄} right-encoded (next {st = s₅} right-read
      (next {st = s₆} right-prepared (next {st = s₇} folded-ok
      (next {st = s₈} exposed end))))))))) = record
      { context = c
      ; begin = a
      ; midpoint = m
      ; finish = b
      ; left-carry = lc
      ; right-carry = rc
      ; statement = final-pis
      ; left-link = record
        { opening = lo
        ; preparation = in-tail (in-tail (in-tail (at-head
            (prepared-at src w s₃ (keys l) (steps l) lhs left-prepared left-pinned left-fields))))
        ; consumptions = in-tail (in-tail (in-tail (in-tail (in-tail (in-tail (in-tail
            (at-head (fold-operand left-member)))))))) All.∷ All.[]
        }
      ; right-link = record
        { opening = ro
        ; preparation = in-tail (in-tail (in-tail (in-tail (in-tail (in-tail (at-head
            (prepared-at src w s₆ (keys r) (steps r) rhs right-prepared right-pinned right-fields)))))))
        ; consumptions = in-tail (in-tail (in-tail (in-tail (in-tail (in-tail (in-tail
            (at-head (fold-operand right-member)))))))) All.∷ All.[]
        }
      }
      where
      open CircuitState using (mem; pis)

      mem₁ = join-memory c a m b lc rc
      mem₃ = apply-writes mem₁ (carry-writes lhs lc)

      published-state : s₁ ≡ published w n c a m b lc rc
      published-state = just-injective (trans (sym publish-ok) (publish-step src w n c a m b lc rc))

      left-encoded-state : s₂ ≡ encoded-state lhs s₁ lc
      left-encoded-state = encode-carried lhs src w s₁ lc
        (cong (λ st → mem st (carry-id lhs)) published-state) left-encoded

      left-read-frame = read-frame src w s₂ (proof-id lhs) left-read

      left-cells : mem s₃ ≡ mem₃
      left-cells = trans (proj₁ left-read-frame)
        (trans (cong mem left-encoded-state)
          (cong (λ st → apply-writes (mem st) (carry-writes lhs lc)) published-state))

      left-limbs = trans
        (cong (λ memory → resolve-all-Fr memory (map var (limbs lhs))) left-cells)
        (resolve-carried-fields lhs (published w n c a m b lc rc) lc)

      left-fields = resolve-child lhs (mem s₃) (steps l) c a m lc left-limbs
        (cong (λ t → t ctx) left-cells) (cong (λ t → t x) left-cells)
        (cong (λ t → t mid) left-cells)

      lp = prepared-step src w s₃ (imm 1ᶠ) (key-digest (keys l)) (ops lhs (steps l))
        (proof-id lhs) (opening-id lhs) left-prepared
      lo = Prepared.opening lp
      mem₄ = ins (opening-id lhs) (val-accumulator lo) mem₃

      left-opening-cells : mem s₄ ≡ mem₄
      left-opening-cells = trans (cong mem (Prepared.after-write lp))
        (cong (ins (opening-id lhs) (val-accumulator lo)) left-cells)

      right-encoded-state : s₅ ≡ encoded-state rhs s₄ rc
      right-encoded-state = encode-carried rhs src w s₄ rc
        (cong (λ t → t (carry-id rhs)) left-opening-cells) right-encoded

      right-read-frame = read-frame src w s₅ (proof-id rhs) right-read
      mem₆ = apply-writes mem₄ (carry-writes rhs rc)

      right-cells : mem s₆ ≡ mem₆
      right-cells = trans (proj₁ right-read-frame)
        (trans (cong mem right-encoded-state)
          (cong (λ memory → apply-writes memory (carry-writes rhs rc)) left-opening-cells))

      right-limbs = trans (cong (λ memory → resolve-all-Fr memory (map var (limbs rhs)))
          (trans (proj₁ right-read-frame) (cong mem right-encoded-state)))
        (resolve-carried-fields rhs s₄ rc)

      right-fields = resolve-child rhs (mem s₆) (steps r) c m b rc right-limbs
        (cong (λ t → t ctx) right-cells) (cong (λ t → t mid) right-cells)
        (cong (λ t → t z) right-cells)

      rp = prepared-step src w s₆ (imm 1ᶠ) (key-digest (keys r)) (ops rhs (steps r))
        (proof-id rhs) (opening-id rhs) right-prepared
      ro = Prepared.opening rp

      right-opening-cells : mem s₇ ≡ ins (opening-id rhs) (val-accumulator ro) mem₆
      right-opening-cells = trans (cong mem (Prepared.after-write rp))
        (cong (ins (opening-id rhs) (val-accumulator ro)) right-cells)

      ff = fold-step src w s₇ fold-ops folded folded-ok

      operand-values : Folded.inputs ff ≡ lo ∷ lc ∷ ro ∷ rc ∷ []
      operand-values = just-injective (trans (sym (Folded.resolved ff))
        (cong (λ memory → resolve-accs memory fold-ops) right-opening-cells))

      left-member : lc ∈ Folded.inputs ff
      left-member = subst (lc ∈_) (sym operand-values) (there (here refl))

      right-member : rc ∈ Folded.inputs ff
      right-member = subst (rc ∈_) (sym operand-values) (there (there (there (here refl))))

      final-pis = trans (cong pis (Exposed.after-expose (expose-step src w s₈ (var folded) exposed)))
        (trans (cong pis (Folded.after-write ff))
          (trans (cong pis (Prepared.after-write rp))
            (trans (proj₂ right-read-frame) (trans (cong pis right-encoded-state)
              (trans (cong pis (Prepared.after-write lp))
                (trans (proj₂ left-read-frame) (trans (cong pis left-encoded-state) (cong pis published-state))))))))

    observe-start : ∀ {start final} (path : Trace src w start (map lower code) final) →
      JoinStart w start → JoinObservation keys l r path
    observe-start path (c , a , m , b , lc , rc , refl) = walked c a m b lc rc path

    observe-run : ∀ final (run : SatisfiedRun src w final) →
      JoinObservation keys l r (SatisfiedRun.path run)
    observe-run final run = observe-start (SatisfiedRun.path run)
      (join-start keys l r w (SatisfiedRun.initialized run))

    bind-statement : ∀ {start final} {path : Trace src w start (map lower code) final} →
      JoinObservation keys l r path → ∀ c a b → CircuitState.pis final ≡ fields n c a b →
      ∃ λ m → ∃ λ lc → ∃ λ rc →
      ChildLink {is = code} path (keys l)
        (instance-fields (lc ∷ []) (fields (steps l) c a m)) (lc ∷ []) ×
      ChildLink {is = code} path (keys r)
        (instance-fields (rc ∷ []) (fields (steps r) c m b)) (rc ∷ [])
    bind-statement observed c a b fields-ok
      with refl , suffix ← ∷-injective (∷-injectiveʳ (trans (sym (JoinObservation.statement observed)) fields-ok))
      with refl , suffix ← ∷-injective suffix
      with refl , _ ← ∷-injective suffix =
      JoinObservation.midpoint observed , JoinObservation.left-carry observed , JoinObservation.right-carry observed ,
      JoinObservation.left-link observed , JoinObservation.right-link observed

observe-join : ∀ keys l r →
  resolve-vk (key-digest (keys l)) (key-table (keys l) (keys r)) ≡ just (keys l) →
  resolve-vk (key-digest (keys r)) (key-table (keys l) (keys r)) ≡ just (keys r) →
  ∀ w final (sat : satisfies (source keys (join l r)) w final) c a b →
  CircuitState.pis final ≡ fields (steps l + steps r) c a b →
  let src = source keys (join l r)
      code = IrSource.instructions src
      path = SatisfiedRun.path (satisfying-run src w final sat)
  in ∃ λ m → ∃ λ lc → ∃ λ rc →
      ChildLink {is = code} path (keys l)
        (instance-fields (lc ∷ []) (fields (steps l) c a m)) (lc ∷ []) ×
      ChildLink {is = code} path (keys r)
        (instance-fields (rc ∷ []) (fields (steps r) c m b)) (rc ∷ [])
observe-join keys l r left-pinned right-pinned w final sat =
  bind-statement (observe-run final (satisfying-run src w final sat))
  where open AtJoin keys l r left-pinned right-pinned w
