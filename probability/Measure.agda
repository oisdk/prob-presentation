module Measure where

import Data.Nat              as ℕ
import Data.Nat.Coprimality  as Coprimality
import Data.Nat.GCD          as GCD
import Data.Nat.Show         as ℕshow
import Data.Nat.Divisibility as Divisibility

open ℕ            using (ℕ; suc; zero)
open Coprimality  using (Coprime)
open Divisibility using (divides)

open import Relation.Nullary.Decidable using (True; False; toWitness; fromWitness)
open import Data.Product using (_,_; ∃; proj₁; proj₂)
open import Data.String as String using (String)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; cong; sym; refl)

open import Data.Empty as ⊥ using (⊥)

record ℙ : Set where
  field
    numerator     : ℕ
    denominator-1 : ℕ
    .coprime      : Coprime numerator (suc denominator-1)

  denominator : ℕ
  denominator = suc denominator-1
open ℙ

infixl 7 _÷₌_
_÷₌_ : (n : ℕ) → (d : ℕ) → .{coprime : Coprime n d} → .{≢0 : False (d ℕ.≟ 0)} → ∃ (λ p → denominator p ≡ d)
numerator     (proj₁ (n ÷₌ _))                 = n
denominator-1 (proj₁ ((_ ÷₌ zero) {≢0 = ()}))
denominator-1 (proj₁ (_ ÷₌ suc d))             = d
coprime       (proj₁ ((_ ÷₌ zero) {≢0 = ()}))
coprime       (proj₁ ((_ ÷₌ suc d) {coprime})) = coprime
proj₂ ((n ÷₌ zero) {≢0 = ()})
proj₂ (n ÷₌ suc d) = refl

infixl 7 _÷_
_÷_ : (n d : ℕ) → .{coprime : Coprime n d} → .{≢0 : False (d ℕ.≟ 0)} → ℙ
numerator (n ÷ d) = n
denominator-1 ((n ÷ zero) {≢0 = ()})
denominator-1 (n ÷ suc d-1) = d-1
coprime ((n ÷ zero) {≢0 = ()})
coprime ((n ÷ suc d-1) {coprime}) = coprime

fromNat : ℕ → ℙ
numerator (fromNat n) = n
denominator-1 (fromNat _) = 0
coprime (fromNat n) = Coprimality.sym (Coprimality.1-coprimeTo n)

private  1+≢*0 : ∀ x y → suc x ≢ y ℕ.* 0
         1+≢*0 x zero ()
         1+≢*0 x (suc y) = 1+≢*0 x y

infixl 7 _?÷₌_
_?÷₌_ : ∀ x y → .{≢0 : False (y ℕ.≟ 0)} → ∃ (λ p → x ℕ.* denominator p ≡ numerator p ℕ.* y)
_?÷₌_ x zero {≢0 = ()}
_?÷₌_ x (suc y-1) with GCD.Bézout.lemma x (suc y-1)
_?÷₌_ x (suc y-1) | GCD.Bézout.result 0 (GCD.GCD.is (_ , divides y′ y-eq) _) _ = ⊥.⊥-elim (1+≢*0 y-1 y′ y-eq)
_?÷₌_ x (suc y-1) | GCD.Bézout.result (suc d-1) (GCD.GCD.is (divides x′ x-eq , divides y′ y-eq) _) bézout = proj₁ frac , eq-prf
  where
    open import Data.Nat using (_*_)

    y = suc y-1
    d = suc d-1

    bézout′ : GCD.Bézout.Identity d (x′ * d) (y′ * d)
    bézout′ = ≡.subst₂ (GCD.Bézout.Identity d) x-eq y-eq bézout


    coprime-prf : Coprime x′ y′
    coprime-prf = Coprimality.Bézout-coprime bézout′

    open ≡.≡-Reasoning
    open import Data.Nat.Properties.Simple

    y′≢0 : False (y′ ℕ.≟ 0)
    y′≢0 = Relation.Nullary.Decidable.fromWitnessFalse wtns
      where
      suc-≢0 : {n : ℕ} → (suc n ≡ 0) → ⊥
      suc-≢0 {n} ()

      open import Relation.Nullary using (¬_)
      wtns : ¬ (y′ ≡ 0)
      wtns refl = suc-≢0 {y-1} y-eq

    frac : ∃ (λ p → denominator p ≡ y′)
    frac = (x′ ÷₌ y′) {coprime = coprime-prf} {≢0 = y′≢0}

    eq-prf : x * denominator (proj₁ frac) ≡ numerator (proj₁ frac) * suc y-1
    eq-prf = begin
      x * denominator (proj₁ frac) ≡⟨ cong (λ z → x * z) (proj₂ frac) ⟩
      x * y′         ≡⟨ cong (λ z → z * y′) x-eq ⟩
      x′ * d * y′    ≡⟨ *-assoc x′ d y′ ⟩
      x′ * (d * y′)  ≡⟨ sym (cong (_*_ x′) (*-comm y′ d)) ⟩
      x′ * (y′ * d)  ≡⟨ sym (cong (_*_ x′) y-eq)  ⟩
      x′ * y ∎

infixl 7 _?÷_
_?÷_ : (x y : ℕ) → .{≢0 : False (y ℕ.≟ 0)} → ℙ
(x ?÷ zero) {≢0 = ()}
x ?÷ suc y-1 with GCD.Bézout.lemma x (suc y-1)
(n ?÷ suc y-1) | GCD.Bézout.result 0 (GCD.GCD.is (_ , divides y′ y-eq) _) _ = ⊥.⊥-elim (1+≢*0 y-1 y′ y-eq)
(n ?÷ suc y-1) | GCD.Bézout.result (suc d-1) (GCD.GCD.is (divides x′ x-eq , divides y′ y-eq) _) bézout = (x′ ÷ y′) {coprime = coprime-prf} {≢0 = y′≢0}
  where
  open import Data.Nat using (_*_)

  y = suc y-1
  d = suc d-1

  bézout′ : GCD.Bézout.Identity d (x′ * d) (y′ * d)
  bézout′ = ≡.subst₂ (GCD.Bézout.Identity d) x-eq y-eq bézout

  coprime-prf : Coprime x′ y′
  coprime-prf = Coprimality.Bézout-coprime bézout′

  y′≢0 : False (y′ ℕ.≟ 0)
  y′≢0 = Relation.Nullary.Decidable.fromWitnessFalse wtns
    where
    suc-≢0 : {n : ℕ} → (suc n ≡ 0) → ⊥
    suc-≢0 {n} ()

    open import Relation.Nullary using (¬_)
    wtns : ¬ (y′ ≡ 0)
    wtns refl = suc-≢0 {y-1} y-eq

_+_ : ℙ → ℙ → ℙ
x + y = ((numerator x ℕ.* denominator y) ℕ.+ (numerator y ℕ.* denominator x)) ?÷ (denominator x ℕ.* denominator y)

_*_ : ℙ → ℙ → ℙ
x * y = (numerator x ℕ.* numerator y) ?÷ (denominator x ℕ.* denominator y)

show : ℙ → String
show p = ℕshow (numerator p) ++ "÷" ++ ℕshow (denominator p)
  where
  open String using (_++_)
  open import Data.Nat.Show renaming (show to ℕshow)
