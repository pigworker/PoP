module Mu where

open import SmolCat

module _ {C : SmolCat}(F : C !> C) where
  open SmolCat.SmolCat
  open SmolFun
  open _->Ty

  MuPre : {D : SmolCat}(F : C !> D) -> Obj D -> Set
  data Mu (x : Obj C) : Set where
    con : MuPre F x -> Mu x

  MuPre (IC r~) x = Mu x
  MuPre (KC P) x = FOBJ P x
  MuPre (F *C G) x = MuPre F x * MuPre G x
  MuPre (PiC A F) x = (a : A) -> MuPre (F a) x
  MuPre (SgC A F) x = A >< \ a -> MuPre (F a) x
  MuPre (G -C F) x = MuPre F (FObj G x)

  
  MuMap : {D : SmolCat}(F : C !> D){S T : Obj D}(f : Arr D S T) -> MuPre F S -> MuPre F T
  MuMap (IC r~)   f (con ss)  = con (MuMap F f ss)
  MuMap (KC G)    f ss        = FARR G f ss
  MuMap (F *C G)  f (fs , gs) = MuMap F f fs , MuMap G f gs
  MuMap (PiC A F) f ss a      = MuMap (F a) f (ss a)
  MuMap (SgC A F) f (a , ss)  = a , MuMap (F a) f ss
  MuMap (G -C F)  f ss        = MuMap F (FArr G f) ss
  
  MuMapId : {D : SmolCat}(F : C !> D){T : Obj D}{f : Arr D T T}(i : Iden D f)
            (ts : MuPre F T) -> MuMap F f ts ~ ts
  MuMapId (IC r~) i (con ts) = con $~ MuMapId F i ts
  MuMapId (KC G) i ts = FIDEN G i ts
  MuMapId (F *C G) i (fs , gs) = _,_ $~ MuMapId F i fs ~$~ MuMapId G i gs
  MuMapId (PiC A G) i ts = ext \ a -> MuMapId (G a) i (ts a)
  MuMapId (SgC A G) i (a , ts) = (a ,_) $~ MuMapId (G a) i ts
  MuMapId (G -C F) i ts = MuMapId F (FIden G i) ts

  MuMapCo : {D : SmolCat}(F : C !> D){R S T : Obj D}
            {f : Arr D R S}{g : Arr D S T}{h : Arr D R T}(c : Comp D f g h)
            (ts : MuPre F R) -> MuMap F h ts ~ MuMap F g (MuMap F f ts)
  MuMapCo (IC r~) c (con ts) = con $~ MuMapCo F c ts
  MuMapCo (KC G) c ts = FCOMP G c ts
  MuMapCo (F *C G) c (fs , gs) = _,_ $~ MuMapCo F c fs ~$~ MuMapCo G c gs
  MuMapCo (PiC A F) c ts = ext \ a -> MuMapCo (F a) c (ts a)
  MuMapCo (SgC A F) c (a , ts) = (a ,_) $~ MuMapCo (F a) c ts
  MuMapCo (G -C F) c ts = MuMapCo F (FComp G c) ts

  MuPRE : C ->Ty
  FOBJ MuPRE = Mu
  FARR MuPRE = MuMap (IC r~)
  FIDEN MuPRE = MuMapId (IC r~)
  FCOMP MuPRE = MuMapCo (IC r~)


