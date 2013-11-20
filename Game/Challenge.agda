{-# OPTIONS --without-K --copatterns #-}
open import Type

module Game.Challenge where

record ChalAdversary (Challenge Response Next : ★) : ★ where
  field
    get-chal : Challenge
    put-resp : Response → Next
open ChalAdversary public

module _ {C R X Y : ★} where
    module MapResponse (f : X → Y) (A : ChalAdversary C R X) where
        A* : ChalAdversary C R Y
        get-chal A*   = get-chal A
        put-resp A* c = f (put-resp A c)

    module MapResponseWithChallenge (f : C → X → Y) (A : ChalAdversary C R X) where
        A* : ChalAdversary C R Y
        get-chal A*   = get-chal A
        put-resp A* c = f (get-chal A) (put-resp A c)
