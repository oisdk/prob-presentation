module Measure where

open import Data.Nat as ℕ
  using (ℕ; suc; zero)
open import Data.Nat.Coprimality as Coprimality
  using (Coprime)

open import Relation.Nullary.Decidable
  using (True; False; toWitness; fromWitness)

record ℙ : Set where
  field
    numerator     : ℕ
    denominator-1 : ℕ
    isCoprime     : True (Coprimality.coprime? numerator (suc denominator-1))

  denominator : ℕ
  denominator = suc denominator-1

  coprime : Coprime numerator denominator
  coprime = toWitness isCoprime

module Simplify where
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; _≢_; cong; sym)
  open import Data.Nat.GCD as GCD using ()
  open import Data.Empty using (⊥-elim)
  open import Data.Nat.Divisibility using (divides)
  open import Data.Product using (_,_)

  record Simp (x : ℕ) (y : ℕ) : Set where
    constructor MkSimp
    field
      x′ y′ : ℕ
      eq-prf : x ℕ.* y′ ≡ x′ ℕ.* y
      coprime-prf : Coprime x′ y′

  1+≢*0 : ∀ x y → suc x ≢ y ℕ.* 0
  1+≢*0 x zero ()
  1+≢*0 x (suc y) = 1+≢*0 x y

  simp : ∀ x y-1 → Simp x (suc y-1)
  simp x y-1 with GCD.Bézout.lemma x (suc y-1)
  simp x y-1 | GCD.Bézout.result 0 (GCD.GCD.is (_ , divides y′ y-eq) _) _ = ⊥-elim (1+≢*0 y-1 y′ y-eq)
  simp x y-1 | GCD.Bézout.result (suc d-1) (GCD.GCD.is (divides x′ x-eq , divides y′ y-eq) _) bézout = MkSimp x′ y′ eq-prf (Coprimality.Bézout-coprime bézout′)
    where
      open import Data.Nat using (_*_)

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

  convOneWay : {n d : ℕ} → True (Coprimality.coprime? n d) → Coprime n d
  convOneWay = toWitness

  convOtherWay : {n : ℕ} → {d : ℕ} → Coprime n d → True (Coprimality.coprime? n d)
  convOtherWay = fromWitness

  _÷_ : (n : ℕ) → (d : ℕ) → {≢0 : False (d ℕ.≟ 0)} → ℙ
  (n ÷ zero ) {≢0 = ()}
  (n ÷ suc d) with simp n d
  (n ÷ suc d) | MkSimp x′ zero _ coprime-prf = record
    { numerator = 1
    ; denominator-1 = zero
    ; isCoprime = convOtherWay (Coprimality.1-coprimeTo (suc zero))
    }
  (n ÷ suc d) | MkSimp x′ (suc y′) _ coprime-prf = record
    { numerator = x′
    ; denominator-1 = y′
    ; isCoprime = convOtherWay coprime-prf
    }
