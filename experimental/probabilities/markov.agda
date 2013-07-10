{-# OPTIONS --without-K #-}
Trans R S = S → M R S
          = S → R → S
          = W R S → S
          = R × S → S

Trans composition

Trans choice

TransFunction R S = R → S
TransFunction = M

if<_then_else_ : [0,1] → S → S → ([0,1] → S)
(if< p then x else y) q = if q <? p then x else y

withPr[_]then_else_ : [0,1] → Trans R S → Trans R S → Trans ([0,1] × R) S
withPr[ p ]then x else y = rand >>= if< p then x else y

data Machine R S ...

run : Machine R S → Trans R S
run ...
