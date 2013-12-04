{-# OPTIONS --without-K --copatterns #-}
open import Type

module Game.Challenge where

record ChalAdversary (Challenge Response Next : ★) : ★ where
  field
    get-chal : Challenge
    put-resp : Response → Next
open ChalAdversary public

module _ {C R N C' R' N' : ★} where
    module Map (chal : C → C')
               (resp : R' → R)
               (next : N → N')
               (A : ChalAdversary C R N) where
        A* : ChalAdversary C' R' N'
        get-chal A*   = chal (get-chal A)
        put-resp A* r = next (put-resp A (resp r))

    module MapWith (chal : C → C')
                   (resp : C → R' → R)
                   (next : C → R  → N → N')
                   (A : ChalAdversary C R N) where
        A* : ChalAdversary C' R' N'
        get-chal A*    = chal (get-chal A)
        put-resp A* r' = next c r (put-resp A r)
           where c = get-chal A
                 r = resp c r'
