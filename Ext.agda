module Ext where

data Zero : Set where
record One : Set where constructor <>
data Two : Set where `0 `1 : Two

record Hide (X : Set) : Set where
  constructor hide
  field
    .seek : X

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 10 _,_

data Sort : Set where prop type : Sort

data U : Sort -> Set
El : {u : Sort} -> U u -> Set

data U where
  `P : U prop -> U type
  `I : U type -> U prop
  `0 : U prop
  `1 : U prop
  `2 : U type
  _`><_ : {u : Sort}(S : U u)(T : El S -> U u) -> U u
  _`->_ : {u : Sort}(S : U type)(T : El S -> U u) -> U u

El T = {!!}
