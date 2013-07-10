{-# OPTIONS --without-K #-}
open import Type
open import Data.List

module Solver.Linear.Syntax {a} (Var : ★_ a) where

  infixr 5 _,_
  data Syn : Set a where
   var : Var → Syn
   tt  : Syn
   _,_ : Syn → Syn → Syn

  infix 4 _↦_

  record Eq : Set a where
    constructor _↦_
    field
      LHS RHS : Syn
  open Eq public

  tuple : Syn → List Syn → Syn
  tuple x []       = x
  tuple x (y ∷ ys) = x , tuple y ys
