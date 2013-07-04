open import Data.Vec as Vec using ([]; _∷_)
open import Text.Parser
open import Data.One
open import Data.Char
open import Data.Nat
open import Data.List
open import Data.Product hiding (map)
open import Data.String as String renaming (toList to S▹L; fromList to L▹S)
open import Solver.Linear.Syntax
open import Data.Maybe.NP hiding (Eq)
open import Relation.Binary.PropositionalEquality

module Solver.Linear.Parser where

spaces : Parser 𝟙
spaces = manyOneOfˢ " \t\n\r" *> pure _

pIdent : Parser String
pIdent = someNoneOfˢ "(,)↦_ \t\n\r" <* spaces

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
parseEqˢ? s = runParser (spaces *> pEqˢ (2 * n) <* eof) ℓ
  where ℓ = S▹L s
        n = length ℓ

parseEqˢ : T[ parseEqˢ? ]
parseEqˢ = F[ parseEqˢ? ]

ex-A⇒B : Eq String
ex-A⇒B = parseEqˢ "A↦B"

ex-𝟙⇒𝟙 : Eq String
ex-𝟙⇒𝟙 = parseEqˢ "𝟙↦𝟙"

ex₁ : Eq String
ex₁ = parseEqˢ " ( A , B,(𝟙,C),(D))↦ B,C , A"

test-ex₁ : ex₁ ≡ ((var"A" , (var"B", (tt , var"C") , var"D"))
                ↦ (var"B" , var"C" , var"A"))
test-ex₁ = refl

-- -}
