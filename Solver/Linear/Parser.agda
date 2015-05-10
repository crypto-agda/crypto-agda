{-# OPTIONS --without-K #-}
open import Data.Vec as Vec using ([]; _∷_)
open import Text.Parser
-- Too slow
-- open import Text.Parser.Heap hiding (Parser) renaming (ParserLC to Parser)
open import Data.One
open import Data.Char
open import Data.Nat.NP
open import Data.List as L
open import Data.Product hiding (map)
open import Data.String as String renaming (toList to S▹L; fromList to L▹S; _++_ to _++S_)
open import Solver.Linear.Syntax
open import Data.Maybe.NP hiding (Eq)
open import Relation.Binary.PropositionalEquality

module Solver.Linear.Parser where

spaces : Parser 𝟙
spaces = manyOneOfˢ " \t\n\r" *> pure _

pIdent : Parser String
pIdent = someNoneOfˢ "(,)↦_𝟙 \t\n\r" <* spaces

tokᶜ : Char → Parser 𝟙
tokᶜ c = char c <* spaces

tokˢ : String → Parser 𝟙
tokˢ s = string s <* spaces

--pPair : ∀ {A B} → Parser A → Parser B → Parser (A × B)
--pPair pA pB = tokᶜ '(' *> ⟪ _,_ · pA <* tokᶜ ',' · pB ⟫ <* tokᶜ ')'

module _ {A} (pA : Parser A) where

    pSimpleSyn pSyn : ℕ → Parser (Syn A)

    pSimpleSyn n =  pure tt <* oneOfˢ "_𝟙"
                ⟨|⟩ tokᶜ '(' *> pSyn n <* tokᶜ ')'
                ⟨|⟩ ⟪ var · pA ⟫

    pSyn zero    = empty
    pSyn (suc n) = ⟪ tuple _ · pSimpleSyn n · many n (tokᶜ ',' *> pSyn n) ⟫

    pEq : ℕ → Parser (Eq A)
    pEq n = ⟪ _↦_ · pSyn n <* tokᶜ '↦' · pSyn n ⟫

pSynˢ : ℕ → Parser (Syn String)
pSynˢ = pSyn pIdent

pEqˢ : ℕ → Parser (Eq String)
pEqˢ = pEq pIdent

parseSynˢ? : String →? Syn String
parseSynˢ? s = runParser (pSynˢ n <* eof) ℓ
  where ℓ = S▹L s
        n = length ℓ

parseSynˢ : T[ parseSynˢ? ]
parseSynˢ = F[ parseSynˢ? ]

parseEqˢ? : String →? Eq String
parseEqˢ? s = runParser (spaces *> pEqˢ (2* n) <* eof) ℓ
  where ℓ = S▹L s
        n = length ℓ

parseEqˢ : T[ parseEqˢ? ]
parseEqˢ = F[ parseEqˢ? ]

ex-A⇒B : Eq String
ex-A⇒B = parseEqˢ "A↦B"

ex-𝟙⇒𝟙 : Eq String
ex-𝟙⇒𝟙 = parseEqˢ "𝟙↦𝟙"

ex-swap : Eq String
ex-swap = parseEqˢ "A,B↦B,A"

ex₁ : Eq String
ex₁ = parseEqˢ " ( A , B,(𝟙,C),(D))↦ B,C , A"

private
  A = var "A"
  B = var "B"
  C = var "C"
  D = var "D"

check-A⇒B : ex-A⇒B ≡ (A ↦ B)
check-A⇒B = refl

check-𝟙⇒𝟙 : ex-𝟙⇒𝟙 ≡ (tt ↦ tt)
check-𝟙⇒𝟙 = refl

check-swap : ex-swap ≡ ((A , B)↦(B , A))
check-swap = refl

check-ex₁ : ex₁ ≡ ((A , (B , (tt , C) , D)) ↦ (B , C , A))
check-ex₁ = refl

alphabet = S▹L "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

rotL : ∀ {A : Set} → ℕ → List A → List A
rotL n xs = drop n xs ++ take n xs

rotS : ℕ → String
rotS n = L▹S (intersperse ',' alphabet ++ '↦' ∷ intersperse ',' (rotL n alphabet))

rotE : ℕ → Eq String
rotE n = tuple0 _ (L.map varC alphabet) ↦ tuple0 _ (L.map varC (rotL n alphabet))
  where varC : Char → Syn String
        varC c = var (L▹S (c ∷ []))

rot13 : Eq String
rot13 = parseEqˢ (rotS 13)

check-rot13 : rot13 ≡ rotE 13
check-rot13 = refl

-- -}
