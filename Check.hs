{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, FlexibleInstances, ExistentialQuantification, ImpredicativeTypes #-}
{- Tests (using QuickChec) patterns of garbled circuit and the simulated circuit are equivalent -}
module Check where

import Test.QuickCheck
import Circuit
import Expr
import Garble
import Proof

instance Show WShape where
  show I = "○"
  show (s :-: t) = "(" ++ (show s) ++ "," ++ (show t) ++ ")"

instance Arbitrary WShape where
  arbitrary = (choose (1,10) :: Gen Int) >>= genShape where
    genShape 1 = return I
    genShape n | n > 1 = do
                   i <- choose (1,n-1)
                   s <- genShape i
                   t <- genShape (n-i)
                   return (s :-: t)

{- The type representing an arbitrary bundle of bits -}
data DynamicWires = forall t. DynWires (Wires Bool t)

instance Arbitrary DynamicWires where
  arbitrary = (choose (1,10) :: Gen Int) >>= genWires where
    genWires :: Int -> Gen DynamicWires
    genWires 1 = do
      b <- choose (True,False)
      return (DynWires (W b))
    genWires n | n > 1 = do
                   i <- choose (1,n-1)
                   (DynWires u) <- genWires i
                   (DynWires v) <- genWires (n-i)
                   return (DynWires (u :+: v))

instance Show DynamicWires where
  show (DynWires w) = show w

{- Generate a random bundle of bits -}
genWires :: WShape -> Gen DynamicWires
genWires I = do
  b <- choose (True,False)
  return (DynWires (W b))
genWires (s :-: t) = do
  (DynWires u) <- genWires s
  (DynWires v) <- genWires t
  return (DynWires (u :+: v))

{- Derive the shape of the output wires given a circuit and its input shape -}
outputShape :: Circuit s t -> WShape -> WShape
outputShape SWAP (u :-: v) = v :-: u
outputShape ASSOC (u :-: (v :-: w)) = ((u :-: v) :-: w)
outputShape UNASSOC ((u :-: v) :-: w) = (u :-: (v :-: w))
outputShape DUP I = I :-: I
outputShape NAND (I :-: I) = I
outputShape (CAT c0 c1) w =
  outputShape c1 (outputShape c0 w)
outputShape (FIRST c) (u :-: w) = (outputShape c u) :-: w

{- The type representing a boolean circuit whose input shape is encoded in s     -}
{- This is called UniformCircuit as the input shape and output shape must agree  -}
{- to the shape of the given input wire. Due to the limitation of Haskell's type -}
{- system, we cannot represent circuits with arbitrary input and output shapes.  -}
{- However, such circuits can still be encoded by adding unused input or output  -}
{- wires.                                                                        -}
type UniformCircuit s = (Wires Bool s, Circuit s s)

{- Generate a random uniform circuit -}
genUniformCircuit :: Wires Bool s -> Gen (UniformCircuit s)
genUniformCircuit (W b) = do
  cs <- elements [0,1] :: Gen Int
  case cs of
    0 -> return (W b, CAT DUP NAND) -- Basic circuits of a single input wire
    1 -> do
      (_,c0) <- genUniformCircuit (W b)
      (_,c1) <- genUniformCircuit (W b)
      return (W b, CAT c0 c1)
genUniformCircuit (W x :+: W y) =
  let w = (W x :+: W y)
      basic = [SWAP, CAT NAND DUP
              -- , CAT (CAT (FIRST DUP) UNASSOC) (second NAND)
              -- , CAT (CAT (second DUP) ASSOC)  (FIRST NAND)
              ]
      -- Basic circuits of input shape (\circ :+: \circ)
  in do
    cs <- elements [0,1,2,3] :: Gen Int
    case cs of
      0 -> elements (Prelude.map (\c -> (w, c)) basic)
      1 -> do
        (_,c0) <- genUniformCircuit (W x)
        return (w,FIRST c0)     -- Use the FIRST combinator
      2 -> do
        (_,c0) <- genUniformCircuit (W y)
        return (w,second c0)    -- Use the SECOND combinator
      3 -> do
        (_,c0) <- genUniformCircuit (W x :+: W y)
        (_,c1) <- genUniformCircuit (W x :+: W y)
        return (w,CAT c0 c1)    -- Use the CAT combinator
genUniformCircuit (W x :+: (W y :+: W z)) =
  let w = (W x :+: (W y :+: W z))
      basic = [CAT ASSOC SWAP
              ,CAT SWAP UNASSOC
              ,CAT ASSOC UNASSOC
               ]
      -- Basic circuits of the input shape (\circ :+: (\circ :+: \circ))
  in do
   cs <- elements [0,1,2,3] :: Gen Int
   case cs of
     0 -> elements (Prelude.map (\c -> (w, c)) basic)
     1 -> do
       (_,c0) <- genUniformCircuit (W x)
       return (w,FIRST c0)
     2 -> do
       (_,c0) <- genUniformCircuit (W y :+: W z)
       return (w,second c0)
     3 -> do
       (_,c0) <- genUniformCircuit (W x :+: (W y :+: W z))
       (_,c1) <- genUniformCircuit (W x :+: (W y :+: W z))
       return (w,CAT c0 c1)
genUniformCircuit ((W x :+: W y) :+: W z) =
  let w = ((W x :+: W y) :+: W z)
      basic = [CAT SWAP ASSOC
              ,CAT UNASSOC SWAP
              ,CAT UNASSOC ASSOC
               ]
      -- Basic circuits of the input shape ((\circ :+: \circ) :+: \circ)
  in do
   cs <- elements [0,1,2,3] :: Gen Int
   case cs of
     0 -> elements (Prelude.map (\c -> (w, c)) basic)
     1 -> do
       (_,c0) <- genUniformCircuit (W x :+: W y)
       return (w,FIRST c0)
     2 -> do
       (_,c0) <- genUniformCircuit (W z)
       return (w,second c0)
     3 -> do
       (_,c0) <- genUniformCircuit ((W x :+: W y) :+: W z)
       (_,c1) <- genUniformCircuit ((W x :+: W y) :+: W z)
       return (w,CAT c0 c1)
-- General input shapes
genUniformCircuit (u :+: v) = 
  let w = (u :+: v) in do
    cs <- elements [1,2,3] :: Gen Int
    case cs of
      1 -> do
        (_,c0) <- genUniformCircuit u
        return (w,FIRST c0)
      2 -> do
        (_,c0) <- genUniformCircuit v
        return (w,second c0)
      3 -> do
        (_,c0) <- genUniformCircuit (u :+: v)
        (_,c1) <- genUniformCircuit (u :+: v)
        return (w,CAT c0 c1)

{- The type that represents an arbitrary uniform circuit -}
data UniformCircuit2 = forall s. UniformCircuit2 (UniformCircuit s)

instance Show UniformCircuit2 where
  show (UniformCircuit2 (w,uc)) = (show w) ++ "\n" ++ (show uc)


{- Generate an arbitrary uniform circuit -}
genUC2 :: DynamicWires -> Gen UniformCircuit2
genUC2 (DynWires w) = do
  wc <- genUniformCircuit w
  return (UniformCircuit2 wc)

instance Arbitrary UniformCircuit2 where
  arbitrary = (arbitrary :: Gen WShape) >>= genWires >>= genUC2


{- QuickCheck property that the pattern of a honest garbled circuit and the -}
{- pattern of a simulated garbled circuit are equivalent up to pseudorandom -}
{- renaming generated in Proof                                              -}
prop_garble (UniformCircuit2 (w,c)) =
  let g = garble c w
      pg = pattern (garbledToPGarbled g)
      (bm,km,v) = gbRenamings c w
      sg = simulate c v w
      psg = pattern (garbledToPGarbled sg)
  in norm (renameKey (renameBit pg bm) km) == norm psg
