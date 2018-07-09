module Measure where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Nat.Coprimality as Coprimality using (Coprime)
open import Relation.Nullary.Decidable using (True; False; toWitness; fromWitness)
open import Data.Product using (_,_; ∃; ∃-syntax; proj₁; proj₂)
open import Data.String as String using (String)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; cong; sym; refl)

record ℙ : Set where
  field
    numerator     : ℕ
    denominator-1 : ℕ
    isCoprime     : True (Coprimality.coprime? numerator (suc denominator-1))

  denominator : ℕ
  denominator = suc denominator-1

  coprime : Coprime numerator denominator
  coprime = toWitness isCoprime
open ℙ

infixl 7 _÷₌_
_÷₌_ : (n : ℕ) → (d : ℕ) → {isCoprime : True (Coprimality.coprime? n d)} → {≢0 : False (d ℕ.≟ 0)} → ∃[ p ] (denominator p ≡ d)
numerator     (proj₁ (n ÷₌ _)                 )= n
denominator-1 (proj₁ ((_ ÷₌ zero) {≢0 = ()}))
denominator-1 (proj₁ (_ ÷₌ suc d)             )= d
isCoprime     (proj₁ ((_ ÷₌ zero) {≢0 = ()}))
isCoprime     (proj₁ ((_ ÷₌ suc d) {isCoprime})) = isCoprime
proj₂ ((n ÷₌ zero) {≢0 = ()})
proj₂ (n ÷₌ suc d) = refl

infixl 7 _÷_
_÷_ : (n d : ℕ) → {isCoprime : True (Coprimality.coprime? n d)} → {≢0 : False (d ℕ.≟ 0)} → ℙ
(n ÷ d) {isCoprime} {≢0} = proj₁ ((n ÷₌ d) {isCoprime} {≢0})

private fromCoprimeWitness : {n d : ℕ} → Coprime n d → True (Coprimality.coprime? n d)
        fromCoprimeWitness = fromWitness

module Simplify where
  open import Data.Nat.GCD as GCD using ()
  open import Data.Empty using (⊥-elim)
  open import Data.Nat.Divisibility using (divides)
  open import Data.Nat using (_*_)
  open import Relation.Nullary
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)

  1+≢*0 : ∀ x y → suc x ≢ y * 0
  1+≢*0 x zero ()
  1+≢*0 x (suc y) = 1+≢*0 x y

  infixl 7 _?÷₌_
  _?÷₌_ : ∀ x y → {≢0 : False (y ℕ.≟ 0)} → ∃[ p ] (x * denominator p ≡ numerator p * y)
  _?÷₌_ x zero {≢0 = ()}
  _?÷₌_ x (suc y-1) with GCD.Bézout.lemma x (suc y-1)
  _?÷₌_ x (suc y-1) | GCD.Bézout.result 0 (GCD.GCD.is (_ , divides y′ y-eq) _) _ = ⊥-elim (1+≢*0 y-1 y′ y-eq)
  _?÷₌_ x (suc y-1) | GCD.Bézout.result (suc d-1) (GCD.GCD.is (divides x′ x-eq , divides y′ y-eq) _) bézout = proj₁ frac , eq-prf
    where
      y = suc y-1
      d = suc d-1

      bézout′ : GCD.Bézout.Identity d (x′ * d) (y′ * d)
      bézout′ = ≡.subst₂ (GCD.Bézout.Identity d) x-eq y-eq bézout


      isCoprime-prf : True (Coprimality.coprime? x′ y′)
      isCoprime-prf = fromCoprimeWitness (Coprimality.Bézout-coprime bézout′)

      open ≡.≡-Reasoning
      open import Data.Nat.Properties.Simple

      y′≢0 : False (y′ ℕ.≟ 0)
      y′≢0 = Relation.Nullary.Decidable.fromWitnessFalse wtns
        where
        suc-≢0 : {n : ℕ} → (suc n ≡ 0) → ⊥
        suc-≢0 {n} ()

        wtns : ¬ (y′ ≡ 0)
        wtns refl = suc-≢0 {y-1} y-eq

      frac : ∃[ p ] (denominator p ≡ y′)
      frac = (x′ ÷₌ y′) {isCoprime = isCoprime-prf} {≢0 = y′≢0}

      eq-prf : x * denominator (proj₁ frac) ≡ numerator (proj₁ frac) * suc y-1
      eq-prf = begin
        x * denominator (proj₁ frac) ≡⟨ cong (λ z → x * z) (proj₂ frac) ⟩
        x * y′         ≡⟨ cong (λ z → z * y′) x-eq ⟩
        x′ * d * y′    ≡⟨ *-assoc x′ d y′ ⟩
        x′ * (d * y′)  ≡⟨ sym (cong (_*_ x′) (*-comm y′ d)) ⟩
        x′ * (y′ * d)  ≡⟨ sym (cong (_*_ x′) y-eq)  ⟩
        x′ * y ∎

fromNat : ℕ → ℙ
numerator (fromNat n) = n
denominator-1 (fromNat _) = 0
isCoprime (fromNat n) = fromCoprimeWitness (Coprimality.sym (Coprimality.1-coprimeTo n))

open Simplify public using (_?÷₌_)

infixl 7 _?÷_
_?÷_ : ℕ → (d : ℕ) → {≢0 : False (d ℕ.≟ 0)} → ℙ
(x ?÷ y) {≢0} = proj₁ ((x ?÷₌ y) {≢0})

_+_ : ℙ → ℙ → ℙ
x + y = (numerator x ℕ.* denominator y ℕ.+ numerator y ℕ.* denominator x) ?÷ (denominator x ℕ.* denominator y)

_*_ : ℙ → ℙ → ℙ
x * y = (numerator x ℕ.* numerator y) ?÷ (denominator x ℕ.* denominator y)

show : ℙ → String
show p = showℕ (numerator p) String.++ "÷" String.++ showℕ (denominator p)
