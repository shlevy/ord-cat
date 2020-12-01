{-# OPTIONS --cubical --no-import-sorts --safe #-}
module OrdCat.Ordinal.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import OrdCat.Ordinal.Base

private
  variable
    e p : Level

-- homogenize-set-goal' :
--   ∀ {ℓ} {T : Type ℓ}
--   {T≡T : T ≡ T}
--   (refl≡T≡T : refl ≡ T≡T)
--   {t : T}
--   (t≡t : PathP (λ i → T≡T i) t t) i →
--   PathP (λ j → refl≡T≡T i j) t t
-- homogenize-set-goal' refl≡T≡T {t = t} t≡t i' =
--   transp
--     (λ i → PathP (λ j → refl≡T≡T ((~ i) ∨ i') j) t t)
--     i'
--     t≡t

-- homogenize-set-goal :
--   ∀ {ℓ} {T : Type ℓ}
--   {T≡T : T ≡ T}
--   (refl≡T≡T : refl ≡ T≡T)
--   {t : T}
--   (t≡t : PathP (λ i → T≡T i) t t) →
--   refl ≡ homogenize-set-goal' refl≡T≡T t≡t i0 →
--   PathP (λ i → PathP (λ j → refl≡T≡T i j) t t) refl t≡t
-- homogenize-set-goal refl≡T≡T {t = t} t≡t goal' i =
--     comp
--       (λ i' → PathP (λ j → refl≡T≡T (i ∧ i') j) t t)
--       (λ j → λ { (i = i0) → refl; (i = i1) → t≡t'≡t≡t j })
--       (goal' i)
--     where
--       t≡t' : t ≡ t
--       t≡t' = homogenize-set-goal' refl≡T≡T t≡t i0

--       t≡t'≡t≡t : PathP (λ i → PathP (λ j → refl≡T≡T i j) t t) t≡t' t≡t
--       t≡t'≡t≡t i' = homogenize-set-goal' refl≡T≡T t≡t i'


module _ {os : OrderStructure {e} {p}} where
  isSet-oe-type→isSet-oe : isSet (os .oe-type) → isSet (OrderElement os)
  isSet-oe-type→isSet-oe isSet-oe-type _ _ x≡₁y x≡₂y = cong (cong oe-inject) (isSet-oe-type _ _ (λ i → x≡₁y i .oe-extract) (λ i → x≡₂y i .oe-extract))

  isProp-≺-type→isProp-≺ : (∀ {x y : os .oe-type} → isProp (os .≺-type x y)) → (∀ {x y : OrderElement os} → isProp (x ≺ y))
  isProp-≺-type→isProp-≺ isProp-≺-type x≺₁y x≺₂y = cong ≺-inject (isProp-≺-type (x≺₁y .≺-extract) (x≺₂y .≺-extract))

  isProp-acc : ∀ {a : OrderElement os} → isProp (acc a)
  isProp-acc (acc-≺ a h₁) (acc-≺ .a h₂) i =
    acc-≺ a (λ b≺a → isProp-acc (h₁ b≺a) (h₂ b≺a) i)

  isProp-well-founded : isProp (well-founded os)
  isProp-well-founded f₁ f₂ i = isProp-acc f₁ f₂ i

open Order

module _ {o : Order {e} {p}} where
  isProp-weakly-extensional : isProp (weakly-extensional (o .order-os))
  isProp-weakly-extensional f₁ f₂ i ≺a↔≺b = o .oe-set _ _ (f₁ ≺a↔≺b) (f₂ ≺a↔≺b) i

os-≡≃o-≡ : ∀ {o₁ o₂ : Order {e} {p}} → (o₁ .Order.order-os ≡ o₂ .Order.order-os) ≃ (o₁ ≡ o₂)
os-≡≃o-≡ .fst os₁≡os₂ i .order-os = os₁≡os₂ i
os-≡≃o-≡ {o₁ = o₁} {o₂ = o₂} .fst os₁≡os₂ i .oe-set = toPathP {A = λ i → isSet (OrderElement (os₁≡os₂ i))} {x = o₁ .oe-set} (isPropIsSet _ (o₂ .oe-set)) i
os-≡≃o-≡ {e} {p} {o₁ = o₁} {o₂ = o₂} .fst os₁≡os₂ i .≺-prop = toPathP {A = λ i → ∀ {x y : OrderElement (os₁≡os₂ i)} → isProp (x ≺ y)} {x = o₁ .≺-prop} (isProp-≺-prop-ty _ (o₂ .≺-prop)) i
  where
    isProp-≺-prop-ty : ∀ {os} → isProp (∀ {x y : OrderElement {e} {p} os} → isProp (x ≺ y))
    isProp-≺-prop-ty f₁ f₂ i = isPropIsProp f₁ f₂ i
os-≡≃o-≡ .snd .equiv-proof o₁≡o₂ .fst .fst i = o₁≡o₂ i .order-os
os-≡≃o-≡ .snd .equiv-proof o₁≡o₂ .fst .snd i j .order-os = o₁≡o₂ j .order-os
os-≡≃o-≡ {o₁ = o₁} {o₂ = o₂} .snd .equiv-proof o₁≡o₂ .fst .snd i j .oe-set = {!!}
os-≡≃o-≡ .snd .equiv-proof o₁≡o₂ .fst .snd i j .≺-prop = {!!}
os-≡≃o-≡ .snd .equiv-proof y .snd fiby = {!!}
-- well-founded-extensional-isSet : isSet (WellFoundedExtensional {s} {r})
-- well-founded-extensional-isSet {s} {r} a b = J (λ b a≡₁b → ∀ a≡₂b → a≡₁b ≡ a≡₂b) refl≡a≡a {b}
--   where
--     module _ (a≡a : a ≡ a) where
--       o : Order {s} {r}
--       o = a .wfext-order

--       o≡o : o ≡ o
--       o≡o i = a≡a i .wfext-order

--       set-ty : Type s
--       set-ty = o .set .fst

--       set-ty≡set-ty : set-ty ≡ set-ty
--       set-ty≡set-ty i = o≡o i .set .fst

--       refl≡set-ty≡set-ty : refl ≡ set-ty≡set-ty
--       refl≡set-ty≡set-ty = isInjectiveTransport transport-refl≡transport-st≡st
--         where
--           instance
--             o' : Order
--             o' = o
--           transport-st≡st-id-acc : ∀ {x} → acc (inject-elem x) → x ≡ transport set-ty≡set-ty x
--           transport-st≡st-id-acc {x} (acc-≺ .(inject-elem x) h) i =
--             a .wfext-weakly-extensional {a = inject-elem x} {b = inject-elem (transport set-ty≡set-ty x)}
--               (λ c → (λ c≺x → let foo = transport-st≡st-id-acc (h (subst (_≺ inject-elem x) inject-extract-id c≺x)) in {!!}) , λ c≺tx → {!!})
--               i
--               .extract-elem

--           transport-refl≡transport-st≡st : transport refl ≡ transport set-ty≡set-ty
--           transport-refl≡transport-st≡st i x = subst (_≡ transport set-ty≡set-ty x) (sym (transportRefl x)) (transport-st≡st-id-acc (a .wfext-well-founded)) i
--           {-
--           transport-≺ : ∀ {a b} → a ≺ b → transport c≡c a ≺ transport c≡c b
--           transport-≺ {a} {b} = transp (λ i → (≺≡≺ i) (transp (λ j → c≡c (j ∧ i)) (~ i) a) (transp (λ j → c≡c (j ∧ i)) (~ i) b)) i0

--           transport⁻-≺ : ∀ {a b} → a ≺ b → transport⁻ c≡c a ≺ transport⁻ c≡c b
--           transport⁻-≺ {a} {b} = transp (λ i → (≺≡≺ (~ i)) (transp (λ j → c≡c (~ (j ∧ i))) (~ i) a) (transp (λ j → c≡c (~ (j ∧ i))) (~ i) b)) i0

--           transport-c-id' : ∀ {a} → acc a → a ≡ transport c≡c a
--           transport-c-id' (order.acc-≺ a h) =
--             wfext-wext _ _
--              (λ c c≺a → subst (_≺ transport c≡c a) (sym (transport-c-id' (h c≺a))) (transport-≺ c≺a))
--                     (λ c c≺ta →
--                        let t⁻c≺a = subst (transport⁻ c≡c c ≺_) (transport⁻Transport c≡c a) (transport⁻-≺ c≺ta)
--                        in subst (_≺ a) (transport-c-id' (h t⁻c≺a) ∙ transportTransport⁻ c≡c c)  t⁻c≺a)

--           transport-c-id : transport refl ≡ transport c≡c
--           transport-c-id i a = subst (_≡ transport c≡c a) (sym (transportRefl a)) (transport-c-id' (wfext-wf a)) i
--           -}


--       refl≡o≡o : refl ≡ o≡o
--       refl≡o≡o i j .set .fst = refl≡set-ty≡set-ty i j
--       refl≡o≡o i j .set .snd = homogenize-set-goal refl≡set-isSet-ty≡set-isSet-ty set-isSet≡set-isSet (isProp→isSet isPropIsSet _ _ _ _) i j
--         where
--           set-isSet-ty : Type s
--           set-isSet-ty = isSet set-ty

--           set-isSet-ty≡set-isSet-ty : set-isSet-ty ≡ set-isSet-ty
--           set-isSet-ty≡set-isSet-ty i = isSet (set-ty≡set-ty i)

--           refl≡set-isSet-ty≡set-isSet-ty : refl ≡ set-isSet-ty≡set-isSet-ty
--           refl≡set-isSet-ty≡set-isSet-ty i j = isSet (refl≡set-ty≡set-ty i j)

--           set-isSet : isSet set-ty
--           set-isSet = o .set .snd

--           set-isSet≡set-isSet : PathP (λ i → set-isSet-ty≡set-isSet-ty i) set-isSet set-isSet
--           set-isSet≡set-isSet i = o≡o i .set .snd
--       refl≡o≡o i j .relation = homogenize-set-goal refl≡relation-ty≡relation-ty rel≡rel (isSet-relation-ty _ _ _ _) i j
--         where
--           relation-ty : Type (ℓ-max s (ℓ-suc r))
--           relation-ty = set-ty → set-ty → hProp r

--           relation-ty≡relation-ty : relation-ty ≡ relation-ty
--           relation-ty≡relation-ty i = (set-ty≡set-ty i) → (set-ty≡set-ty i) → hProp r

--           refl≡relation-ty≡relation-ty : refl ≡ relation-ty≡relation-ty
--           refl≡relation-ty≡relation-ty i j = (refl≡set-ty≡set-ty i j) → (refl≡set-ty≡set-ty i j) → hProp r

--           rel : set-ty → set-ty → hProp r
--           rel = o .relation

--           rel≡rel : PathP (λ i → relation-ty≡relation-ty i) rel rel
--           rel≡rel i = o≡o i .relation

--           isSet-relation-ty : isSet relation-ty
--           isSet-relation-ty x y x≡₁y x≡₂y i j a b = isSetHProp (x a b) (y a b) (λ j → x≡₁y j a b) (λ j → x≡₂y j a b) i j

--       refl≡a≡a : refl ≡ a≡a
--       refl≡a≡a i j .wfext-order = refl≡o≡o i j
--       refl≡a≡a i j .wfext-well-founded = homogenize-set-goal refl≡wf-ty≡wf-ty wf≡wf (isProp→isSet (well-founded-isProp ⦃ o = o ⦄) _ _ _ _) i j
--         where
--           wf-ty : Type (ℓ-max s r)
--           wf-ty = well-founded ⦃ o = o ⦄

--           wf-ty≡wf-ty : wf-ty ≡ wf-ty
--           wf-ty≡wf-ty i = well-founded ⦃ o = o≡o i ⦄

--           refl≡wf-ty≡wf-ty : refl ≡ wf-ty≡wf-ty
--           refl≡wf-ty≡wf-ty i j = well-founded ⦃ o = refl≡o≡o i j ⦄

--           wf : wf-ty
--           wf = a .wfext-well-founded

--           wf≡wf : PathP (λ i → wf-ty≡wf-ty i) wf wf
--           wf≡wf i = a≡a i .wfext-well-founded
--       refl≡a≡a i j .wfext-weakly-extensional = homogenize-set-goal refl≡wext-ty≡wext-ty wext≡wext (isProp→isSet (weakly-extensional-isProp ⦃ o = o ⦄) _ _ _ _) i j
--         where
--           wext-ty : Type (ℓ-max s r)
--           wext-ty = weakly-extensional ⦃ o = o ⦄

--           wext-ty≡wext-ty : wext-ty ≡ wext-ty
--           wext-ty≡wext-ty i = weakly-extensional ⦃ o = o≡o i ⦄

--           refl≡wext-ty≡wext-ty : refl ≡ wext-ty≡wext-ty
--           refl≡wext-ty≡wext-ty i j = weakly-extensional ⦃ o = refl≡o≡o i j ⦄

--           wext : wext-ty
--           wext = a .wfext-weakly-extensional

--           wext≡wext : PathP (λ i → wext-ty≡wext-ty i) wext wext
--           wext≡wext i = a≡a i .wfext-weakly-extensional
