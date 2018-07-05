module Measure where

open import Data.Nat as ℕ
  using (ℕ; suc; zero)
open import Data.Nat.Show renaming (show to showℕ)

open import Data.Nat.Coprimality as Coprimality
  using (Coprime)

open import Relation.Nullary.Decidable
  using (True; False; toWitness; fromWitness)

open import Data.Product
  using (_,_; ∃; ∃-syntax; proj₁; proj₂)

open import Data.String as String
  using (String)

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

module Simplify where
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; cong; sym)
  open import Data.Nat.GCD as GCD using ()
  open import Data.Empty using (⊥-elim)
  open import Data.Nat.Divisibility using (divides)
  open import Data.Product using (_,_)
  open import Data.Nat using (_*_)

  record Simp (x : ℕ) (y : ℕ) : Set where
    constructor MkSimp
    field
      x′ y′ : ℕ
      eq-prf : x * y′ ≡ x′ * y
      coprime-prf : Coprime x′ y′

  1+≢*0 : ∀ x y → suc x ≢ y * 0
  1+≢*0 x zero ()
  1+≢*0 x (suc y) = 1+≢*0 x y

  simp : ∀ x y-1 → Simp x (suc y-1)
  simp x y-1 with GCD.Bézout.lemma x (suc y-1)
  simp x y-1 | GCD.Bézout.result 0 (GCD.GCD.is (_ , divides y′ y-eq) _) _ = ⊥-elim (1+≢*0 y-1 y′ y-eq)
  simp x y-1 | GCD.Bézout.result (suc d-1) (GCD.GCD.is (divides x′ x-eq , divides y′ y-eq) _) bézout = MkSimp x′ y′ eq-prf (Coprimality.Bézout-coprime bézout′)
    where
      y = suc y-1
      d = suc d-1

      bézout′ : GCD.Bézout.Identity d (x′ * d) (y′ * d)
      bézout′ = ≡.subst₂ (GCD.Bézout.Identity d) x-eq y-eq bézout

      open ≡.≡-Reasoning
      open import Data.Nat.Properties.Simple

      eq-prf : x * y′ ≡ x′ * y
      eq-prf = begin
        x * y′         ≡⟨ cong (λ z → z * y′) x-eq ⟩
        x′ * d * y′    ≡⟨ *-assoc x′ d y′ ⟩
        x′ * (d * y′)  ≡⟨ sym (cong (_*_ x′) (*-comm y′ d)) ⟩
        x′ * (y′ * d)  ≡⟨ sym (cong (_*_ x′) y-eq)  ⟩
        x′ * y         ∎

  fromCoprimeWitness : {n : ℕ} → {d : ℕ} → Coprime n d → True (Coprimality.coprime? n d)
  fromCoprimeWitness = fromWitness

  open ℙ

  infixl 7 _÷₌_
  _÷₌_ : (n : ℕ) → (d : ℕ) → {≢0 : False (d ℕ.≟ 0)} → ∃[ p ] (n * denominator p ≡ numerator p * d)
  (n ÷₌ zero ) {≢0 = ()}
  (n ÷₌ suc d) with simp n d
  (n ÷₌ suc d) | MkSimp x′ (suc y′) e coprime-prf = record
    { fst = record
      { numerator = x′
      ; denominator-1 = y′
      ; isCoprime = fromCoprimeWitness coprime-prf
      }
    ; snd = e
    }
  (n ÷₌ suc d) | MkSimp x′ zero e coprime-prf with Coprimality.0-coprimeTo-1 (Coprimality.sym coprime-prf)
  (n ÷₌ suc d) | MkSimp .1 zero e coprime-prf | ≡.refl with 1+≢*0 (d ℕ.+ 0) n (≡.sym e)
  (n ÷₌ suc d) | MkSimp .1 zero e coprime-prf | ≡.refl | ()

  fromNat : ℕ → ℙ
  fromNat n = record
    { numerator = n
    ; denominator-1 = zero
    ; isCoprime = fromCoprimeWitness (Coprimality.sym (Coprimality.1-coprimeTo n))
    }

open Simplify public using (_÷₌_; fromNat)

infixl 7 _÷_
_÷_ : ℕ → (d : ℕ) → {≢0 : False (d ℕ.≟ 0)} → ℙ
(x ÷ y) {≢0} = proj₁ ((x ÷₌ y) {≢0})

_+_ : ℙ → ℙ → ℙ
x + y = (numerator x ℕ.* denominator y ℕ.+ numerator y ℕ.* denominator x) ÷ (denominator x ℕ.* denominator y)

_*_ : ℙ → ℙ → ℙ
x * y = (numerator x ℕ.* numerator y) ÷ (denominator x ℕ.* denominator y)

show : ℙ → String
show p = showℕ (numerator p) String.++ "÷" String.++ showℕ (denominator p)
