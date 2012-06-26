module STLC.EContext where

open import STLC.Base
open import STLC.SSubst

_▸▸_ : Con → Con → Con
v1 ▸▸ ε        = v1
v1 ▸▸ (y , y') = (v1 ▸▸ y) , y'


--up' {ε} {Δ} t  = up t
--up' {y , y'} t = wkTm vz {!!}