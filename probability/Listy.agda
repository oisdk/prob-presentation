module Listy where

open import Measure
open import Data.List as List using (List; []; _∷_)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Nat as ℕ using (ℕ; suc; zero)

open import Function

record Prob (A : Set) : Set where
  constructor weighted
  field
    runProb : List (A × ℙ)

open Prob

open import Category.Monad

monad : RawMonad Prob
monad = record
    { return = λ x → weighted ((x , fromNat 1) ∷ [])
    ; _>>=_  = bind
    }
  where
  import Data.List.Categorical
  open RawMonad Data.List.Categorical.monad
  bind : {A B : Set} → Prob A → (A → Prob B) → Prob B
  bind xs f = weighted do
    (x , xp) ← runProb xs
    (y , yp) ← runProb (f x)
    return (y , xp * yp)

support : {A : Set} → Prob A → List A
support = List.map proj₁ ∘ runProb

expect : {A : Set} → (A → ℙ) → Prob A → ℙ
expect p = List.foldl (λ ys y → ys + (p (proj₁ y) * (proj₂ y)) ) (fromNat 0) ∘ runProb

open import Data.Bool using (Bool; if_then_else_)

probOf : {A : Set} → (A → Bool) → Prob A → ℙ
probOf p = expect (λ x → if p x then fromNat 1 else fromNat 0)

uniform : {A : Set} → List A → Prob A
uniform [] = weighted []
uniform (x ∷ xs) = weighted (List.map (flip _,_ p) (x ∷ xs))
  where
  p : ℙ
  p = 1 ?÷ (suc (List.length xs))

open import Data.Fin as Fin using (Fin)

enumerate : (n : ℕ) → List (Fin n)
enumerate zero = []
enumerate (suc n) = Fin.zero ∷ List.map Fin.suc (enumerate n)

module Die where
  die : Prob (Fin 6)
  die = uniform (enumerate 6)

  open RawMonad monad

  pairadice : Prob ℕ
  pairadice = do
    x ← die
    y ← die
    return (suc (Fin.toℕ x) ℕ.+ suc (Fin.toℕ y))

open import Data.String using (String)
open import Relation.Nullary.Decidable using (⌊_⌋)

example : String
example = show (probOf (λ x → ⌊ x ℕ.≟ 7 ⌋) Die.pairadice)
