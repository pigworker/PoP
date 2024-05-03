module SmolCat where

module _ {l}{X : Set l} where

 data _~_ (x : X) : X -> Set where
   r~ : x ~ x

 infix 40 _-~-_
 infix 41 _~o

 _~o : forall {x y} -> x ~ y -> y ~ x                 -- symmetry
 r~ ~o = r~

 _-~-_ : forall {x y z} -> x ~ y -> y ~ z -> x ~ z    -- transitivity
 r~ -~- q = q

 infixr 30 _~[_>_ _<_]~_
 infixr 31 _[QED]

 _~[_>_ : forall x {y z} -> x ~ y -> y ~ z -> x ~ z
 x ~[ q0 > q1 = q0 -~- q1

 _<_]~_ : forall x {y z} -> y ~ x -> y ~ z -> x ~ z
 x < q0 ]~ q1 = q0 ~o -~- q1

 _[QED] : forall x -> x ~ x
 x [QED] = r~

{-# BUILTIN EQUALITY _~_ #-}

rf : forall {k}{X : Set k} (x : X) -> x ~ x
rf x = r~

Pr : Set -> Set
Pr X = (a b : X) -> a ~ b

postulate
  ext : {A : Set}{B : A -> Set}{f g : (a : A) -> B a}
     -> ((a : A) -> f a ~ g a)
     -> f ~ g

module _ {k l}{X : Set k}{Y : Set l} where
 
 infixl 2 _~$~_ _$~_ _~$   -- "associating to the left, rather as we all did
                           -- in the sixties" (Roger Hindley)
  
 _~$~_ : {f g : X -> Y}{a b : X} -> f ~ g -> a ~ b -> f a ~ g b
 r~ ~$~ r~ = r~
  
 _$~_ : {a b : X}            (f : X -> Y) -> a ~ b -> f a ~ f b
 f $~ q = rf f ~$~ q

 _~$ : {f g : X -> Y}{a : X} ->     f ~ g          -> f a ~ g a
 f ~$ = f ~$~ r~

record One : Set where constructor <>

record _><_ (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open _><_ public
infixr 10 _,_

_*_ : Set -> Set -> Set
S * T = S >< \ _ -> T

<_> : {X : Set} -> (X -> Set) -> Set
< P > = _ >< P

record SmolCat : Set1 where
  field
    Obj   : Set
    Arr   : Obj -> Obj -> Set
    Iden  : forall {X} -> Arr X X -> Set
    iden  : forall {X} -> < Iden {X} >
    UIden : forall {X} -> Pr < Iden {X} >
    Comp  : forall {R S T} -> Arr R S -> Arr S T -> Arr R T -> Set
    comp  : forall {R S T}(f : Arr R S)(g : Arr S T) -> < Comp f g >
    UComp : forall {R S T}{f : Arr R S}{g : Arr S T} -> Pr < Comp f g >
    absl  : forall {S T}{i : Arr S S}{f : Arr S T}
         -> Iden i -> Comp i f f
    absr  : forall {S T}{f : Arr S T}{i : Arr T T}
         -> Iden i -> Comp f i f
    asso  : forall {R S T U}
            {rs : Arr R S}{rt : Arr R T}{ru : Arr R U}
            {st : Arr S T}{su : Arr S U}{tu : Arr T U}
         -> Comp rs st rt -> Comp st tu su -> Comp rs su ru
         -> Comp rt tu ru
  
  asso03 : forall {R S T U}
            {rs : Arr R S}{rt : Arr R T}
            {st : Arr S T}{su : Arr S U}{tu : Arr T U}
         -> Comp rs st rt -> Comp st tu su
         -> Arr R U >< \ ru -> Comp rs su ru * Comp rt tu ru
  asso03 {rs = rs} {su = su} rst stu
    with ru , rsu <- comp rs su = ru , rsu , asso rst stu rsu
  

module _ (C : SmolCat) where
  open SmolCat

  _-op : SmolCat
  Obj _-op = Obj C
  Arr _-op S T = Arr C T S
  Iden _-op = Iden C
  iden _-op = iden C
  UIden _-op = UIden C
  Comp _-op f g h = Comp C g f h
  comp _-op f g = comp C g f
  UComp _-op = UComp C
  absl _-op = absr C
  absr _-op = absl C
  asso _-op rst stu rsu
    with _ , rtu , rsu' <- asso03 C stu rst
    with r~ <- UComp C (_ , rsu) (_ , rsu')
       = rtu

module _ (C D : SmolCat) where
  open SmolCat
  record SmolFun : Set where
    field
      FObj  : Obj C -> Obj D
      FArr  : forall {S T : Obj C}
           -> Arr C S T -> Arr D (FObj S) (FObj T)
      FIden : forall {X : Obj C}{i : Arr C X X}
           -> Iden C i -> Iden D (FArr i)
      FComp : forall {R S T : Obj C}
              {f : Arr C R S}{g : Arr C S T}{h : Arr C R T}
           -> Comp C f g h
           -> Comp D (FArr f) (FArr g) (FArr h)

module _ (C : SmolCat) where
  open SmolCat C
  record _->Ty : Set1 where
    field
      FOBJ  : Obj -> Set
      FARR  : forall {S T} -> Arr S T -> FOBJ S -> FOBJ T
      FIDEN : forall {X}{i : Arr X X} -> Iden i ->
               (x : FOBJ X) -> FARR i x ~ x
      FCOMP : forall {R S T : Obj}
              {f : Arr R S}{g : Arr S T}{h : Arr R T}
           -> Comp f g h
           -> (r : FOBJ R) -> FARR h r ~ FARR g (FARR f r)

  open _->Ty
  Hom : Obj -> _->Ty
  FOBJ (Hom X) Y = Arr X Y
  FARR (Hom X) g f = fst (comp f g)
  FIDEN (Hom X) {i = i} I f
    with v <- comp f i
    with r~ <- UComp v (_ , absr I)
       = r~
  FCOMP (Hom X) {f = f} {g} {h} u k
    with kf , v <- comp k f
       | kh , w <- comp k h
    with x <- comp kf g
    with r~ <- UComp (_ , asso v u w) x
    = r~

module _ {C D : SmolCat}(F : SmolFun C D)(P : D ->Ty) where

  open SmolCat
  open SmolFun F
  open _->Ty

  Pre : C ->Ty
  FOBJ  Pre X = FOBJ P (FObj X)
  FARR  Pre f = FARR P (FArr f)
  FIDEN Pre I = FIDEN P (FIden I) 
  FCOMP Pre v = FCOMP P (FComp v)

module _ {D : SmolCat}(A : Set)(B : A -> D ->Ty) where
  open SmolCat D
  open _->Ty

  Sg : D ->Ty
  FOBJ Sg X = A >< \ a -> FOBJ (B a) X
  FARR Sg f (a , BS) = a , FARR (B a) f BS
  FIDEN Sg I (a , BX) = (a ,_) $~ FIDEN (B a) I BX
  FCOMP Sg v (a , BR) = (a ,_) $~ FCOMP (B a) v BR

  Pi : D ->Ty
  FOBJ Pi X = (a : A) -> FOBJ (B a) X
  FARR Pi f BS a = FARR (B a) f (BS a)
  FIDEN Pi I BX = ext \ a -> FIDEN (B a) I (BX a)
  FCOMP Pi v BR = ext \ a -> FCOMP (B a) v (BR a)

module _ {D : SmolCat} where
  open SmolCat D
  open _->Ty

  ONE : D ->Ty
  FOBJ ONE _ = One
  FARR ONE = _
  FIDEN ONE _ _ = r~
  FCOMP ONE _ _ = r~

  PRD : D ->Ty -> D ->Ty -> D ->Ty
  FOBJ (PRD F G) X = FOBJ F X * FOBJ G X
  FARR (PRD F G) k (FS , GS) = FARR F k FS , FARR G k GS
  FIDEN (PRD F G) I (FX , GX) = _,_ $~ FIDEN F I FX ~$~ FIDEN G I GX
  FCOMP (PRD F G) v (FR , GR) = _,_ $~ FCOMP F v FR ~$~ FCOMP G v GR

data _!>_ (C D : SmolCat) : Set1 where
  IC : C ~ D -> C !> D
  KC : D ->Ty -> C !> D
  _*C_ : C !> D -> C !> D -> C !> D
  PiC SgC : (A : Set) -> (A -> C !> D) -> C !> D
  _-C_ : forall {E} -> SmolFun D E -> C !> E -> C !> D

[_]C : forall {C D} -> C !> D -> C ->Ty -> D ->Ty
[ IC r~ ]C X = X
[ KC G ]C X = G
[ F *C G ]C X = PRD ([ F ]C X) ([ G ]C X)
[ PiC A F ]C X = Pi A \ a -> [ F a ]C X
[ SgC A F ]C X = Sg A \ a -> [ F a ]C X
[ R -C F ]C X = Pre R ([ F ]C X)

module _ {C : SmolCat} (F : C !> C) where
  open SmolCat
  open SmolFun
  open _->Ty


{-
  {-# TERMINATING #-}
  MU : C ->Ty
  {-# NO_POSITIVITY_CHECK #-}
  data Mu (x : Obj C) : Set where
    con : FOBJ ([ F ]C MU) x -> Mu x
  FOBJ MU = Mu
  FARR MU f (con ss) = con (FARR ([ F ]C MU) f ss)
  FIDEN MU ii (con ss) = con $~ (FIDEN ([ F ]C MU) ii ss)
  FCOMP MU cc (con rr) = con $~ (FCOMP ([ F ]C MU) cc rr)


module _ (C : SmolCat) where
  open SmolCat

  data AQ {S T}(f : Arr C S T) :
    {S' T' : Obj C} -> S ~ S' -> T ~ T' -> Arr C S' T' -> Set where
    rAQ : AQ f r~ r~ f

module _ (C : SmolCat) where
  open SmolCat
  open SmolFun

  record _->SmolCat : Set1 where
    field
      COBJ : Obj C -> SmolCat
      CARR : {S T : Obj C} -> Arr C S T ->
             SmolFun (COBJ S) (COBJ T)
      CIDEN : {X : Obj C}{i : Arr C X X}(I : Iden C i) ->
              ((Y : Obj (COBJ X)) ->  FObj (CARR i) Y ~ Y) >< \ oq ->
              {S T : Obj (COBJ X)}(f : Arr (COBJ X) S T) ->
                 AQ (COBJ X) (FArr (CARR i) f) (oq S) (oq T) f
      CCOMP : {R S T : Obj C}
        {f : Arr C R S}{g : Arr C S T}{h : Arr C R T}
        -> Comp C f g h
        -> ((X : Obj (COBJ R)) ->
            FObj (CARR h) X ~ FObj (CARR g) (FObj (CARR f) X))
            >< \ oq ->
        {A B : Obj (COBJ R)}(p : Arr (COBJ R) A B) ->
        AQ (COBJ T)
           (FArr (CARR h) p)
           (oq A) (oq B)
           (FArr (CARR g) (FArr (CARR f) p))

module _ (C : SmolCat)(F : C ->SmolCat)  where
  open SmolCat
  open SmolFun
  open _->SmolCat F

  aqLem : (c : Obj C)
          (x : Obj (COBJ c))
          (xj' : Arr (COBJ c) x x)
          (w : Obj (COBJ c))(q : w ~ x)
          (xj : Arr (COBJ c) w x)
          (xq : AQ (COBJ c) xj q r~ xj')
          (yj : Arr (COBJ c) w x)
          (yq : AQ (COBJ c) yj q r~ xj') ->
          _~_ {_} {Arr (COBJ c) w x >< \ a -> AQ (COBJ c) a q r~ xj'}
            (xj , xq) (yj , yq)
  aqLem c x xj' .x r~ .xj' rAQ .xj' rAQ = r~

  aqLem' : (c : Obj C)
          (x x' : Obj (COBJ c))
          (xj' : Arr (COBJ c) x x')
          (w : Obj (COBJ c))(q : w ~ x)
          (xj : Arr (COBJ c) w x')
          (xq : AQ (COBJ c) xj q r~ xj')
          (yj : Arr (COBJ c) w x')
          (yq : AQ (COBJ c) yj q r~ xj') ->
          _~_ {_} {Arr (COBJ c) w x' >< \ a -> AQ (COBJ c) a q r~ xj'}
            (xj , xq) (yj , yq)
  aqLem' c x x' xj' .x r~ .xj' rAQ .xj' rAQ = r~
-}

{-
  SG : SmolCat
  Obj SG = Obj C >< \ c -> Obj (COBJ c)
  Arr SG (c , x) (d , y) =
    Arr C c d >< \ f -> 
    Arr (COBJ d) (FObj (CARR f) x) y
  Iden SG {c , x} (i , j) =
    Iden C i >< \ I -> 
    Arr (COBJ c) x x >< \ j' ->
    AQ (COBJ c) j (fst (CIDEN I) x ) r~ j' *
    Iden (COBJ c) j'
  fst (fst (iden SG {c , x})) = fst (iden C {c})
  snd (fst (iden SG {c , x}))
    with i , I <- iden C {c}
    with y <- FObj (CARR i) x
       | r~ <- fst (CIDEN I) x
       = fst (iden (COBJ c) {x})
  fst (snd (iden SG {c , x})) = snd (iden C {c})
  fst (snd (snd (iden SG {c , x}))) = fst (iden (COBJ c) {x})
  snd (snd (snd (iden SG {c , x})))
    with i , I <- iden C {c}
    with y <- FObj (CARR i) x
       | r~ <- fst (CIDEN I) x
    with j , J <- iden (COBJ c) {x}
       = rAQ , J
  UIden SG {c , x}
    ((xi , xj) , xI , xj' , xq , xJ)
    ((yi , yj) , yI , yj' , yq , yJ)
    with r~ <- UIden C (xi , xI) (yi , yI)
    with r~ <- UIden (COBJ c) (xj' , xJ) (yj' , yJ)
    with r~ <- aqLem' c x x xj'
             (FObj (CARR xi) x) (fst (CIDEN xI) x) xj xq yj yq
       = r~

  Comp SG {c , x}{d , y}{e , z} (f , f') (g , g') (h , h') = 
    Comp C f g h >< \ v ->
    Arr (COBJ e) (FObj (CARR h) x) (FObj (CARR g) y) >< \ f'' ->
    AQ (COBJ e) f'' (fst (CCOMP v) x) r~ (FArr (CARR g) f') *
    Comp (COBJ e) f'' g' h'
  fst (fst (comp SG {c , x} {d , y} {e , z} (f , f') (g , g')))
    = fst (comp C f g)
  snd (fst (comp SG {c , x} {d , y} {e , z} (f , f') (g , g')))
    with h , v <- comp C f g
    with _  <- FObj (CARR h) x
       | r~ <- fst (CCOMP v) x
    = fst (comp (COBJ e) (FArr (CARR g) f') g')
  fst (snd (comp SG {c , x} {d , y} {e , z} (f , f') (g , g')))
    = snd (comp C f g)
  fst (snd (snd (comp SG {c , x} {d , y} {e , z} (f , f') (g , g'))))
    with h , v <- comp C f g
    with _  <- FObj (CARR h) x
       | r~ <- fst (CCOMP v) x
       = FArr (CARR g) f'
  snd (snd (snd (comp SG {c , x} {d , y} {e , z} (f , f') (g , g'))))
    with h , v <- comp C f g
    with _  <- FObj (CARR h) x
       | r~ <- fst (CCOMP v) x
    with h' , w <- comp (COBJ e) (FArr (CARR g) f') g'
       = rAQ , w
  UComp SG {c , x} {d , y} {e , z} {f , f'} {g , g'}
    ((xi , xj) , xv , xj' , xq , xw)
    ((yi , yj) , yv , yj' , yq , yw)
    with r~ <- UComp C (_ , xv) (_ , yv)
    with r~ <- aqLem' e  _ _ (FArr (CARR g) f') _ (fst (CCOMP xv) x) xj' xq yj' yq
    with r~ <- UComp (COBJ e) (_ , xw) (_ , yw)
    = r~
  fst (absl SG {i = i , j} {f , g} (I , j' , q , J)) = absl C I
  fst (snd (absl SG {c , x} {d , y} {i , j} {f , g} (I , j' , q , J))) = FArr (CARR f) j'
  fst (snd (snd (absl SG {c , x} {d , y} {i , j} {f , g} (I , j' , q , J))))
       with q' <- fst (CIDEN I) x
       = {!fst (CCOMP (absl C I)) x!}
  snd (snd (snd (absl SG {c , x} {d , y} {i , j} {f , g} (I , j' , q , J)))) = absl (COBJ d) (FIden (CARR f) J)
  absr SG = {!!}
  asso SG = {!!}


-}
