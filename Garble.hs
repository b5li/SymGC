{-# LANGUAGE GADTs, DataKinds, TypeOperators, DeriveFunctor #-}
{- Symbolic garbling procedures and simulator -}
module Garble where

import Control.Monad.State.Lazy
import Circuit
import Expr

type GTEntryS   = EncS (EncS (BitS :*: KeyS))
type GTable = Exp ((GTEntryS :*: GTEntryS) :*: (GTEntryS :*: GTEntryS))
type WLabel = Exp (BitS :*: (KeyS :*: KeyS))

data GC = EmptyGC | Table GTable | GC :/: GC

-- Utility functions to extract bits and keys from a label
wlabel_bit :: WLabel -> Exp BitS
wlabel_bit (Pair b _) = b

wlabel_key0 :: WLabel -> Exp KeyS
wlabel_key0 (Pair _ (Pair k0 _)) = k0

wlabel_key1 :: WLabel -> Exp KeyS
wlabel_key1 (Pair _ (Pair _ k1)) = k1

{- Simple Monad to create new wire labels -}
newtype WireM a = Wrap { unWrap :: State Int a } deriving Functor 
instance Applicative WireM where
  pure v = Wrap (pure v)
  (Wrap f) <*> (Wrap x) = Wrap (f <*> x)
instance Monad WireM where
  x >>= f = Wrap (unWrap x >>= (unWrap . f))
  return x = Wrap $ state (\s -> (x,s))

getWireLabel :: WireM WLabel
getWireLabel = Wrap $ do
  c <- get
  put (c+1)
  return $ Pair (VarB c) (Pair (VarK (2*c)) (VarK (2*c+1)))

evalWireM :: WireM a -> a
evalWireM (Wrap m) = evalState m 0

{- The core of circuit garbler -}
gb :: Circuit x y -> Wires WLabel x -> WireM (Wires WLabel y, GC)
gb SWAP (x :+: y) = pure (y :+: x, EmptyGC)
gb ASSOC (x :+: (y :+: z)) = pure ((x :+: y) :+: z, EmptyGC)
gb UNASSOC ((x :+: y) :+: z) = pure (x :+: (y :+: z), EmptyGC)
gb (CAT c0 c1) x = do
  (y, gc0) <- gb c0 x
  (z, gc1) <- gb c1 y
  return (z,gc0 :/: gc1)
gb (FIRST c) (x :+: y) = do
  (z,gc) <- gb c x
  return (z :+: y, gc)
gb DUP (W (Pair b (Pair k0 k1))) =
  let w0 = W (Pair b (Pair (PRG0 k0) (PRG0 k1)))
      w1 = W (Pair b (Pair (PRG1 k0) (PRG1 k1)))
  in pure (w0 :+: w1, EmptyGC)
gb NAND (W w0 :+: W w1) = do 
  w2 <- getWireLabel
  return (W w2, Table $ gbTable w0 w1 w2)

gbTable :: WLabel -> WLabel -> WLabel -> GTable
gbTable (Pair b0 (Pair k00 k01))
        (Pair b1 (Pair k10 k11))
        (Pair b2 (Pair k20 k21)) =
  Perm b0 (Perm b1 (Enc k00 (Enc k10 (Pair (Not b2) k21)))
                   (Enc k00 (Enc k11 (Pair (Not b2) k21))))
          (Perm b1 (Enc k01 (Enc k10 (Pair (Not b2) k21)))
                   (Enc k01 (Enc k11 (Pair (    b2) k20))))           

ginput :: Wires WLabel s -> Wires Bool s -> Wires (Exp (BitS :*: KeyS)) s
ginput (W l) (W b) = W $ Pair b' k where
  b' = if b then Not (wlabel_bit l) else (wlabel_bit l)
  k  = (if b then wlabel_key1 else wlabel_key0) l
ginput (ls :+: lr) (bs :+: br) =
  (ginput ls bs) :+: (ginput lr br)

gmask :: Wires WLabel t -> Wires (Exp (BitS)) t
gmask (W w) = W (wlabel_bit w)
gmask (ws :+: wr) =
  (gmask ws) :+: (gmask wr)


{- A circuit example -}
c_example = (CAT (CAT (FIRST DUP) UNASSOC) (CAT (CAT SWAP (FIRST NAND)) SWAP))

{- The core of the simulator -}
sim :: Circuit s t -> Wires WLabel s -> WireM (Wires WLabel t, GC)
sim SWAP    (x :+: y)         = pure (y :+: x, EmptyGC)
sim ASSOC   (x :+: (y :+: z)) = pure ((x :+: y) :+: z, EmptyGC)
sim UNASSOC ((x :+: y) :+: z) = pure (x :+: (y :+: z), EmptyGC)
sim (CAT c0 c1) x = do
  (y,gc0) <- sim c0 x
  (z,gc1) <- sim c1 y
  return (z, gc0 :/: gc1)
sim (FIRST c) (x :+: y) = do
  (z,gc) <- sim c x
  return (z :+: y, gc)
sim DUP (W (Pair b (Pair k0 k1))) =
  let w0 = W (Pair b (Pair (PRG0 k0) (PRG0 k1)))
      w1 = W (Pair b (Pair (PRG1 k0) (PRG1 k1)))
  in pure (w0 :+: w1, EmptyGC)
sim NAND (W w0 :+: W w1) = do
  w2 <- getWireLabel
  return (W w2, Table $ simTable w0 w1 w2)

simTable :: WLabel -> WLabel -> WLabel -> GTable
simTable (Pair b0 (Pair k00 k01))
         (Pair b1 (Pair k10 k11))
         (Pair b2 (Pair k20 k21)) =
  Perm b0 (Perm b1 (Enc k00 (Enc k10 (Pair b2 k20)))
                   (Enc k00 (Enc k11 (Pair b2 k20))))
          (Perm b1 (Enc k01 (Enc k10 (Pair b2 k20)))
                   (Enc k01 (Enc k11 (Pair b2 k20))))

{- Generate the output mapping of simulated GC given the output value of a circuit -}
simMask :: Wires WLabel s -> Wires Bool s -> Wires (Exp (BitS)) s
simMask (W w) (W y) = 
  let b = wlabel_bit w
  in W (if y then (Not b) else b)
simMask (ws :+: wr) (ys :+: yr) = (simMask ws ys) :+: (simMask wr yr)

{- Generate the input encoding for the simulator -}
simInput :: Wires WLabel s -> Wires (Exp (BitS :*: KeyS)) s
simInput (W w) = W (Pair (wlabel_bit w) (wlabel_key0 w))
simInput (ws :+: wr) =
  (simInput ws) :+: (simInput wr)

{- Generate a bundle of labels for input wires -}
{- Ideally this function should take a shape instead of a bundle of boolean -}
getInputLabel :: Wires Bool s -> WireM (Wires WLabel s)
getInputLabel (W b) = do
  w <- getWireLabel
  return $ W w
getInputLabel (bs :+: br) = do
  ws <- getInputLabel bs
  wr <- getInputLabel br
  return $ ws :+: wr

{- Output data structure of garble/simulate -}
data Garbled s t = Garbled {
  garbled_c :: GC,                            -- garbled circuit
  garbled_x :: Wires (Exp (BitS :*: KeyS)) s, -- garbled input
  garbled_m :: Wires (Exp BitS) t             -- garbled output map
  } deriving (Show,Eq)

{- Garbling procedure -}
garble :: Circuit s t -> Wires Bool s -> Garbled s t
garble c x = (Garbled gc gx gm) where
  genGC = do
    u      <- getInputLabel x
    (v,gc) <- gb c u
    return (gc,u,v)
  (gc,u,v) = evalWireM genGC
  gx = ginput u x
  gm = gmask v
  
{- Simulator -}
simulate :: Circuit s t  ->
            Wires Bool t ->
            Wires Bool s ->     -- Ideally this should be extracted from circuit
            Garbled s t
simulate c y ux = (Garbled gc gx gm) where
  simGC = do
    u      <- getInputLabel ux
    (v,gc) <- sim c u
    return (gc,u,v)
  (gc,u,v) = evalWireM simGC
  gx = simInput u
  gm = simMask v y 

unmask :: Wires (Exp (BitS :*: KeyS)) s -> Wires (Exp BitS) s -> Wires Bool s
unmask (W (Pair b k)) (W m) = W (b `xor` m)
unmask (ws :+: wr) (bs :+: br) = (unmask ws bs) :+: (unmask wr br)

{- Evaluator -}
evalGarbled :: Circuit s t ->
               Garbled s t ->
               Wires Bool t
evalGarbled c (Garbled gc gx m) = unmask (gEv c gc gx) m where
  {- Core of evaluator -}
  gEv :: Circuit s t                     -> -- circuit topology
         GC                              -> -- garbled circuit
         Wires (Exp (BitS :*: KeyS)) s   -> -- garbled input
         Wires (Exp (BitS :*: KeyS)) t      -- garbled output
  gEv SWAP  EmptyGC (u :+: v) = (v :+: u)
  gEv ASSOC EmptyGC (u :+: (v :+: w)) = ((u :+: v) :+: w)
  gEv UNASSOC EmptyGC ((u :+: v) :+: w) = (u :+: (v :+: w))
  gEv DUP   EmptyGC (W (Pair b k)) = (W (Pair b (PRG0 k)) :+: W (Pair b (PRG1 k)))
  gEv NAND  (Table gt) (W (Pair b0 k0) :+: W (Pair b1 k1)) =
    let row   = proj gt b0 in
    let entry = proj row b1 in
    let pair = dec k1 (dec k0 entry) in
    W pair
  gEv (CAT c0 c1) (gc0 :/: gc1) u =
    let w = gEv c0 gc0 u in
    gEv c1 gc1 w
  gEv (FIRST c) gc (u :+: v) = (gEv c gc u) :+: v

instance Show GC where
  show EmptyGC = "eps"
  show (Table gt) = show gt
  show (gc0 :/: gc1) = (show gc0) ++ ", " ++ (show gc1)

instance Eq GC where
  EmptyGC == EmptyGC = True
  Table gt0 == Table gt1 = gt0 == gt1
  (gc0 :/: gc1) == (gc0' :/: gc1') = (gc0 == gc0') && (gc1 == gc1')
  x == y = False
  
  
