module VectorClockFunctional where

open import Postulates
open import Event
open import HappensBefore
open import Clock
open import Data.Bool using (true;false)
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as ℕ
open import Data.Nat.Properties as NatProp
open import Data.Product using (_×_; ∃-syntax; _,_;proj₁;proj₂)
open import Data.Vec.Functional as Vector hiding (init)
open import Data.Vec.Functional.Properties as VectorProp
import Data.Vec.Functional.Relation.Binary.Equality.Setoid as VectorEq
open import Data.Vec.Functional.Relation.Binary.Pointwise
import Data.Vec.Functional.Relation.Binary.Pointwise.Properties as Pointwiseₚ
open import Data.Sum using (_⊎_;inj₁;inj₂)
open import Function using (const)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality using (refl;_≅_;_≇_;≅-to-≡) renaming(cong to hetero-cong;subst to hetero-subst)
open import Relation.Binary.PropositionalEquality as Eq using (refl;_≡_;subst;sym;cong;cong-app;_≢_) 
open import Relation.Nullary using (¬_;_because_;ofⁿ;ofʸ;yes;no)

open VectorEq (DecSetoid.setoid  NatProp.≡-decSetoid)

private
  variable
    pid pid′ pid″ : ProcessId
    eid eid′ eid″ : LocalEventId
    m  : Message
    e  : Event pid  eid
    e′ : Event pid′ eid′
    e″ : Event pid″ eid″

VC : Set
VC = Vector ℕ n

private
  variable
    vc vc′ vc″ : VC

 -- converting from Event to VC

vc[_] : Event pid eid → VC
vc[_] {pid} init        = updateAt pid (const 1) (replicate 0)
vc[_] {pid} (send _ e)  = updateAt pid suc vc[ e ]
vc[_] {pid} (recv e e′) = updateAt pid suc (zipWith _⊔_ vc[ e ] vc[ e′ ])

 -- lemmas about Vector functions

updateAt-updates-suc : ∀ m → suc (vc m) ≡ updateAt m suc vc m
updateAt-updates-suc {vc} m = sym (updateAt-updates m vc)

zip⊔-monotonicˡ : ∀ (vc : VC) (vc′ : VC) m → vc′ m ≤ zipWith _⊔_ vc′ vc m
zip⊔-monotonicˡ vc vc′ m = m≤m⊔n (vc′ m) (vc m)

zip⊔-monotonicʳ : ∀ (vc : VC) (vc′ : VC) m  → vc m ≤ zipWith _⊔_ vc′ vc m
zip⊔-monotonicʳ vc vc′ m = m≤n⊔m (vc′ m) (vc m)

 -- lemmas about VC

_≈_ : VC → VC → Set
_≈_ = _≋_

≈-refl : vc ≈ vc
≈-refl = ≋-refl

_≺_ : VC → VC → Set
vc ≺ vc′ = Pointwise _≤_ vc vc′ × ∃[ pid ] vc pid < vc′ pid

≺-irrefl : ¬ vc ≺ vc
≺-irrefl (_ , _ , x) = <-irrefl refl x

≺-trans : vc ≺ vc′ → vc′ ≺ vc″ → vc ≺ vc″
≺-trans (x , _) (y , z , w) = (λ i → ≤-trans (x i) (y i)) , z , <-transʳ (x z) w

vc[p]-<⇒≇ : ∀ pid → vc pid < vc′ pid → vc ≇ vc′
vc[p]-<⇒≇ pid vc[pid]<vc′[pid] vc≅vc′ = <⇒≢ vc[pid]<vc′[pid] (cong-app (≅-to-≡ vc≅vc′) pid)

vc-≺⇒≇ : vc ≺ vc′ → vc ≇ vc′
vc-≺⇒≇ (_ , pid , vc[pid]<vc′[pid] ) vc≅vc′ = vc[p]-<⇒≇ pid vc[pid]<vc′[pid] vc≅vc′

 -- lemmas about vc[_]

vc[e]pid⊔bv[e′]pid<vc[recv[e,e′]]pid : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′) → vc[ e ] pid[ e′ ] ⊔ vc[ e′ ] pid[ e′ ] < vc[ recv e e′ ] pid[ e′ ]
vc[e]pid⊔bv[e′]pid<vc[recv[e,e′]]pid e e′ = subst (vc[ e ] pid[ e′ ] ⊔ vc[ e′ ] pid[ e′ ] <_) (updateAt-updates-suc pid[ e′ ]) ≤-refl

vc[e]pid<vc[recv[e,e′]]pid : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′) → vc[ e ] pid[ e′ ] < vc[ recv e e′ ] pid[ e′ ]
vc[e]pid<vc[recv[e,e′]]pid e e′ = <-transʳ (zip⊔-monotonicˡ vc[ e′ ] vc[ e ] pid[ e′ ]) (vc[e]pid⊔bv[e′]pid<vc[recv[e,e′]]pid e e′)

vc[e′]pid<vc[recv[e,e′]]pid : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′) → vc[ e′ ] pid[ e′ ] < vc[ recv e e′ ] pid[ e′ ]
vc[e′]pid<vc[recv[e,e′]]pid e e′ = <-transʳ (zip⊔-monotonicʳ vc[ e′ ] vc[ e ]  pid[ e′ ]) (vc[e]pid⊔bv[e′]pid<vc[recv[e,e′]]pid e e′)

vc[e]pid<vc[send[e]]pid : ∀ {pid eid} (e : Event pid eid) m → vc[ e ] pid[ e ] < vc[ send m e ] pid[ e ] 
vc[e]pid<vc[send[e]]pid e _ = subst (vc[ e ] pid[ e ] <_) (updateAt-updates-suc pid[ e ]) ≤-refl

vc[init]pid≡1 : ∀ {pid} → vc[ init {pid} ] pid ≡ 1
vc[init]pid≡1 {pid} = updateAt-updates pid (replicate 0)

pid≢i⇒vc[e]⊔vc[e′]i≡vc[recv[e,e′]]i : ∀ {pid pid′ eid eid′} (e : Event pid eid) (e′ : Event pid′ eid′) i → i ≢ pid[ e′ ] →  (zipWith _⊔_ vc[ e ] vc[ e′ ]) i ≡ vc[ recv e e′ ] i
pid≢i⇒vc[e]⊔vc[e′]i≡vc[recv[e,e′]]i e e′ i i≢pid = sym (updateAt-minimal i pid[ e′ ] (zipWith _⊔_ vc[ e ] vc[ e′ ]) i≢pid)

pid≢i⇒vc[e′]i≤vc[recv[e,e′]]i : ∀ {pid pid′ eid eid′}(e : Event pid eid) (e′ : Event pid′ eid′) i → i ≢ pid[ e′ ] → vc[ e′ ] i ≤ vc[ recv e e′ ] i
pid≢i⇒vc[e′]i≤vc[recv[e,e′]]i e e′ i i≢pid = subst ( vc[ e′ ] i ≤_) (pid≢i⇒vc[e]⊔vc[e′]i≡vc[recv[e,e′]]i e e′ i i≢pid ) (zip⊔-monotonicʳ vc[ e′ ] vc[ e ] i)

pid≢i⇒vc[e]i≤vc[recv[e,e′]]i : ∀ {pid pid′ eid eid′}(e : Event pid eid) (e′ : Event pid′ eid′) i → i ≢ pid[ e′ ] → vc[ e ] i ≤ vc[ recv e e′ ] i
pid≢i⇒vc[e]i≤vc[recv[e,e′]]i e e′ i i≢pid = subst (vc[ e ] i ≤_) (pid≢i⇒vc[e]⊔vc[e′]i≡vc[recv[e,e′]]i e e′ i i≢pid) ((zip⊔-monotonicˡ vc[ e′ ] vc[ e ] i))

pid≢i⇒vc[send[e]]i≡vc[e]i : ∀{pid eid } (e : Event pid eid) m i → i ≢ pid[ e ] → vc[ send m e ] i ≡ vc[ e ] i
pid≢i⇒vc[send[e]]i≡vc[e]i e _ i i≢pid = updateAt-minimal i pid[ e ] vc[ e ] i≢pid

pid≢i⇒vc[init]i≡0 : ∀ {pid} i → i ≢ pid → vc[ init {pid} ] i ≡ 0
pid≢i⇒vc[init]i≡0 {pid} i i≢pid = updateAt-minimal i pid (replicate 0) i≢pid

0<vc[e]pid[e] : 0 < vc[ e ] pid[ e ]
0<vc[e]pid[e] {pid} e@{e = init}    = subst (0 <_) (sym vc[init]pid≡1) (s≤s z≤n)
0<vc[e]pid[e] {pid} {e = send x e}  = subst (0 <_) (sym (updateAt-updates pid vc[ e ])) (<-trans (0<vc[e]pid[e]{e = e}) (s≤s ≤-refl))
0<vc[e]pid[e] {pid} {e = recv e e′} = <-trans (<-transˡ (0<vc[e]pid[e] {e = e′}) (zip⊔-monotonicʳ vc[ e′ ] vc[ e ] pid)) (vc[e]pid⊔bv[e′]pid<vc[recv[e,e′]]pid e e′)

 -- Clock definition

clock : Clock
clock = record
  { C        = VC
  ; C[_]     = vc[_]
  ; _≺_      = _≺_
  ; ≺-trans  = ≺-trans
  }

open ⊏-PreservingRules
open ⊏-DeterminingRules

clock-⊏-preserving-rules : ⊏-PreservingRules clock
⊏-preserving-rule₁ clock-⊏-preserving-rules {e = e} {m = m} = lemma , pid[ e ] , vc[e]pid<vc[send[e]]pid e m
  where
   lemma : Pointwise _≤_ vc[ e ] vc[ send m e ]
   lemma i with i Fin.≟ pid[ e ]
   ... | yes x rewrite x  = <⇒≤ (vc[e]pid<vc[send[e]]pid e m)
   ... | no x rewrite pid≢i⇒vc[send[e]]i≡vc[e]i e m i x = ≤-refl 
⊏-preserving-rule₂ clock-⊏-preserving-rules {e = e} {e′ = e′} = lemma , pid[ e ] , (vc[e′]pid<vc[recv[e,e′]]pid e′ e)
  where
   lemma : Pointwise _≤_ vc[ e ] vc[ recv e′ e ]
   lemma i with i Fin.≟ pid[ e ]
   ... | yes x rewrite x  = <⇒≤ (vc[e′]pid<vc[recv[e,e′]]pid e′ e ) 
   ... | no x = pid≢i⇒vc[e′]i≤vc[recv[e,e′]]i e′ e i x
⊏-preserving-rule₃ clock-⊏-preserving-rules {e = e} {e′ = e′} = lemma , pid[ e′ ] , (vc[e]pid<vc[recv[e,e′]]pid e e′)
  where
   lemma : Pointwise _≤_ vc[ e ] vc[ recv e e′ ]
   lemma i with i Fin.≟ pid[ e′ ]
   ... | yes x rewrite x  = <⇒≤ (vc[e]pid<vc[recv[e,e′]]pid e e′)
   ... | no x = pid≢i⇒vc[e]i≤vc[recv[e,e′]]i e e′ i x

-- other lemmas about vc[_]

⊏-preserving-index : e ⊏ e′ →  vc[ e ] pid[ e′ ] < vc[ e′ ] pid[ e′ ]
⊏-preserving-index {e = e} {e′ = send m e}  processOrder₁       = vc[e]pid<vc[send[e]]pid e m
⊏-preserving-index {e = e} {e′ = recv e′ e} processOrder₂      = vc[e′]pid<vc[recv[e,e′]]pid e′ e
⊏-preserving-index {e = e} {e′ = recv e e′} send⊏recv          = vc[e]pid<vc[recv[e,e′]]pid e e′
⊏-preserving-index (trans {_} {_} {_} {_} {_} {_} {pid″} x y)  = <-transʳ (proj₁ ((⊏-PreservingRules-sufficient clock) clock-⊏-preserving-rules x) pid″) (⊏-preserving-index y)

⊏-determining-index : pid[ e ] ≢ pid[ e′ ] → vc[ e ] pid[ e ] ≤ vc[ e′ ] pid[ e ] → e ⊏ e′
⊏-determining-index {e = e} e′@{e′ = init} x y = ⊥-elim (≤⇒≯ y (subst ( vc[ e ] pid[ e ] >_) z (0<vc[e]pid[e] {e = e})))
  where
   z : 0 ≡ vc[ e′ ] pid[ e ]
   z = sym (pid≢i⇒vc[init]i≡0 pid[ e ] x)
⊏-determining-index {e = e} {e′ = send m e′} x y = trans (⊏-determining-index x (subst (vc[ e ] pid[ e ] ≤_) z y)) processOrder₁
  where
   z : vc[ send m e′ ] pid[ e ] ≡ vc[ e′ ] pid[ e ]
   z = pid≢i⇒vc[send[e]]i≡vc[e]i e′ m pid[ e ] x
⊏-determining-index {e = e} {e′ = recv e″ e′} x y
  with z ← subst ( vc[ e ] pid[ e ] ≤_ ) (sym (pid≢i⇒vc[e]⊔vc[e′]i≡vc[recv[e,e′]]i e″ e′ pid[ e ] x)) y -- vc[ e ] pid[ e ] ≤ vc[ e″ ] pid[ e ] ⊔ vc[ e′ ] pid[ e ]
  with vc[ e″ ] pid[ e ] ≤? vc[ e′ ] pid[ e ]
...| yes w
     with u ← subst ( vc[ e ] pid[ e ] ≤_ ) (m≤n⇒m⊔n≡n w) z -- vc[ e ] pid[ e ] ≤ vc[ e′ ] pid[ e ] 
     = trans (⊏-determining-index x u) processOrder₂
...| no w
     with u ← subst ( vc[ e ] pid[ e ] ≤_ ) (m≥n⇒m⊔n≡m (<⇒≤ (≰⇒> w))) z -- vc[ e ] pid[ e ] ≤ vc[ e″ ] pid[ e ]  
     with pid[ e ] Fin.≟ pid[ e″ ]
...   | no v = trans (⊏-determining-index v u) send⊏recv
...   | yes refl with ⊏-tri-locally {e = e} {e′ = e″} refl 
...            | inj₁ v = trans v send⊏recv
...            | inj₂ (inj₁ refl) = send⊏recv
...            | inj₂ (inj₂ v) = ⊥-elim (<⇒≱ (⊏-preserving-index v) u)

-- potential determining rules?
⊏-determining-index-init : pid[ e ] ≢ pid[ e′ ] → e′ ≡ init → vc[ e ] pid[ e ] ≤ vc[ e′ ] pid[ e ] → e ⊏ e′
⊏-determining-index-init {e = e} {e′ = e′} x refl y = ⊥-elim (≤⇒≯ y (subst ( vc[ e ] pid[ e ] >_) z (0<vc[e]pid[e] {e = e})))
  where
   z : 0 ≡ vc[ e′ ] pid[ e ]
   z = sym (pid≢i⇒vc[init]i≡0 pid[ e ] x)
⊏-determining-index-recv : pid[ e ] ≢ pid[ e′ ] → vc[ e ] pid[ e ] ≤ vc[ recv e″ e′ ] pid[ e ] → e ⊏ e′
⊏-determining-index-send : pid[ e ] ≢ pid[ e′ ] → vc[ e ] pid[ e ] ≤ vc[ send m e′ ] pid[ e ] → e ⊏ e′

⊏-determining-index-send {e = e} e′@{e′ = init}       {m = m} x y rewrite pid≢i⇒vc[send[e]]i≡vc[e]i e′ m pid[ e ] x = ⊏-determining-index-init x refl y
⊏-determining-index-send {e = e} e′@{e′ = send m″ e″} {m = m} x y rewrite pid≢i⇒vc[send[e]]i≡vc[e]i e′ m pid[ e ] x = trans (⊏-determining-index-send {m = m} x y) processOrder₁
⊏-determining-index-send {e = e} e′@{e′ = recv e″ e‴} {m = m} x y rewrite pid≢i⇒vc[send[e]]i≡vc[e]i e′ m pid[ e ] x = trans (⊏-determining-index-recv {e″ = e″} x y) processOrder₂

⊏-determining-index-recv {e = e} e′@{e′ = init}       {e″ = e″} x y = {!!}
⊏-determining-index-recv {e = e} e′@{e′ = send m e‴}  {e″ = e″} x y = {!!}
⊏-determining-index-recv {e = e} e′@{e′ = recv e⁗ e‴} {e″ = e″} x y = {!!}

lemma₁ : ∀ (e : Event pid eid) (e′ : Event pid′ eid′) →
         pid[ e ] ≢ pid[ e′ ] → vc[ e ] ≺ vc[ e′ ] → vc[ e ] pid[ e′ ] < vc[ e′ ] pid[ e′ ]
lemma₁ e e′@init x (∀≤ , _) = ⊥-elim (≤⇒≯ (∀≤ pid[ e ]) (subst ( vc[ e ] pid[ e ] >_) z (0<vc[e]pid[e] {e = e})))
  where
   z : 0 ≡ vc[ e′ ] pid[ e ]
   z = sym (pid≢i⇒vc[init]i≡0 pid[ e ] x)
lemma₁ e (send m e′) x y = {!!}
lemma₁ e (recv e′ e″) x y = {!!}

-- current rules
clock-⊏-determining-rules : ⊏-DeterminingRules clock
⊏-determining-rule₁ clock-⊏-determining-rules {e = e} {e′ = e′} refl eid≤ (∀≤ , pid , p<p)
 with ⊏-tri-locally {e = e} {e′ = e′} refl
... | inj₁ x        = ≤⇒≯ eid≤ (⊏⇒eid<-locally refl x)
... | inj₂ (inj₁ refl) = <⇒≢ p<p refl
... | inj₂ (inj₂ y) = ≤⇒≯ (∀≤ pid[ e ]) (⊏-preserving-index y)
-- possible lemma : ∀(e : Event pid eid) → vc[ e ] pid[ e ] ≡ eid[ e ]
⊏-determining-rule₂ clock-⊏-determining-rules {e = e} e′@{e′ = init} pid≢ x (∀≤ , ∃<) = <⇒≱ (0<vc[e]pid[e] {e = e})(subst (_≥ vc[ e ] pid[ e ]) vc[e′]pid[e] (∀≤ pid[ e ]))
  where
    vc[e′]pid[e] : vc[ e′ ] pid[ e ] ≡ 0
    vc[e′]pid[e] = updateAt-minimal pid[ e ] pid[ e′ ] (replicate 0) pid≢
-- ⊏-determining-rule₃ clock-⊏-determining-rules {e = e} {e′ = e′} {m = m} pid≢ x y = x e⊏e′
--   where
--     e⊏send[e′] : e ⊏ send m e′
--     e⊏send[e′] = ⊏-determining-index pid≢ (proj₁ y pid[ e ])
--     e⊏e′ : e ⊏ e′
--     e⊏e′ with ⊏-inv₁ e⊏send[e′] 
--     ... | inj₁ refl = ⊥-elim (pid≢ refl)
--     ... | inj₂ y = y
-- incomplete direct proof attempt
⊏-determining-rule₃ clock-⊏-determining-rules {e = e} {e′ = e′} {m = m} pid≢ x y@(∀≤ , p , p<p) = {!!}
  where
    -- this lemma can simplify the proof
    lemma : Pointwise _≤_ vc[ e ] vc[ e′ ]
    lemma i with i Fin.≟ pid[ e′ ]
    ... | yes refl = bar (subst (suc (vc[ e ] i) ≤_) (sym (updateAt-updates-suc i)) (lemma₁ e (send m e′)  pid≢ y))
      where bar : ∀{a b} → suc a ≤ suc b → a ≤ b
            bar (s≤s x) = x
    lemma i | no z  = subst (vc[ e ] i ≤_) (updateAt-minimal i pid[ e′ ] vc[ e′ ] z) (∀≤ i)

-- maybe helpful? ∀ pid[ e ] ≢ pid[ e′ ] → e ⊏ e′ → ∃[ e″ ]recv e e″ ⊏  e′

⊏-determining-rule₄ clock-⊏-determining-rules {e = e} {e′ = e′} {e″ = e″} pid≢ x y z w = x e⊏e′
  where
    e⊏recv[e″,e′] : e ⊏ recv e″ e′
    e⊏recv[e″,e′] =  ⊏-determining-index pid≢ (proj₁ w pid[ e ])
    e⊏e′ : e ⊏ e′
    e⊏e′ with ⊏-inv₂ e⊏recv[e″,e′]
    ... | inj₁ (inj₁ v) = ⊥-elim (z v)
    ... | inj₁ (inj₂ v) = ⊥-elim (y v)
    ... | inj₂ (inj₁ refl) = ⊥-elim (pid≢ refl)
    ... | inj₂ (inj₂ v) = v

postulate
  a : vc[ e ] ≺ vc[ e′ ] → vc[ e ] pid[ e′ ] < vc[ e′ ] pid[ e′ ]
  b : pid[ e ] ≢ pid[ e′ ] → vc[ e ] pid[ e′ ] < vc[ send m e′ ] pid[ e′ ] →  vc[ e ] pid[ e′ ] < vc[ e′ ] pid[ e′ ]
  
experiment : pid[ e ] ≢ pid[ e′ ] → vc[ e ] ≺ vc[ send m e′ ] →  vc[ e ] ≺ vc[ e′ ]
experiment {e = e} e′@{e′ = init} {m = m} pid≢ (∀≤ , _) = ⊥-elim (<⇒≱ (0<vc[e]pid[e] {e = e}) (x pid[ e ] pid≢))
  where
    x : ∀ i → i ≢ pid[ e′ ] → vc[ e ] i ≤ 0
    x i i≢ = subst (vc[ e ] i ≤_) (Eq.trans (pid≢i⇒vc[send[e]]i≡vc[e]i e′ m i i≢) (pid≢i⇒vc[init]i≡0 i i≢)) (∀≤ i)
experiment {e = e} {e′ = send m e′} pid≢ x = {!x!}
experiment {e′ = recv e′ e′₁} pid≢ x = {!!}

