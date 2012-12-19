open import Type
open import Search.Type
open import Search.Searchable

module dice where

data Dice : ★₀ where
  ⚀ ⚁ ⚂ ⚃ ⚄ ⚅ : Dice

searchDice : ∀ m → Search m Dice
searchDice m _∙_ f = f ⚀ ∙ (f ⚁ ∙ (f ⚂ ∙ (f ⚃ ∙ (f ⚄ ∙ f ⚅))))

searchDice-ind : ∀ {m} p → SearchInd p (searchDice m)
searchDice-ind p P _∙_ f = f ⚀ ∙ (f ⚁ ∙ (f ⚂ ∙ (f ⚃ ∙ (f ⚄ ∙ f ⚅))))

μDice : Searchable Dice
μDice = _ , searchDice-ind _
