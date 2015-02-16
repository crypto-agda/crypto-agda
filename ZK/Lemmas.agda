open import ZK.Types
open import Data.Two.Base hiding (_==_)
open import Relation.Binary.PropositionalEquality.NP

module ZK.Lemmas
         {G ℤq}
         (cg : Cyclic-group G ℤq)
         (cg-props : Cyclic-group-properties cg)
         (open Cyclic-group cg)
         (open Cyclic-group-properties cg-props)
         (c₀ c₁ : ℤq)(f₀ f₁ : ℤq)(A : G)(u : G)
         (g' : G)
         (v0 : ✓ (g' ^ f₀ == A · u ^ c₀))
         (v1 : ✓ (g' ^ f₁ == A · u ^ c₁))
         where

  open ≡-Reasoning
  private
    w = dlog g' u
    fd = f₀ - f₁
    cd = c₀ - c₁

    .pf : _
    pf = (g' ^ w) ^ cd
       ≡⟨ ap₂ _^_ (dlog-ok g' u) idp ⟩
         u ^ cd
       ≡⟨ ^-- ⟩
         (u ^ c₀) / (u ^ c₁)
       ≡⟨ ! cancels-/ ⟩
         (A · (u ^ c₀)) / (A · (u ^ c₁))
       ≡⟨ ap₂ _/_ (! ==-✓ v0) (! ==-✓ v1) ⟩
         (g' ^ f₀) / (g' ^ f₁)
       ≡⟨ ! ^-- ⟩
         g' ^ fd
       ∎

  .proof : g' ^(fd * modinv cd) ≡ u
  proof = ! ap (_^_ g') (left-*-to-right-/ (^-inj (^-* ∙ pf))) ∙ dlog-ok g' u
