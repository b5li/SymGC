{-# LANGUAGE GADTs, DataKinds, KindSignatures, TypeOperators, DeriveGeneric #-}
{- Symbolic expressions and patterns -}
module Expr where

import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import qualified Data.Hashable as Hashable
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Bits as Bits
import qualified Data.IntMap.Lazy as IntMap

data Shape = EmptyS | BitS | KeyS | EncS Shape | Shape :*: Shape
  deriving (Eq, Generic)

data Exp (s :: Shape) where
  Bit  :: Bool -> Exp BitS
  VarB :: Int  -> Exp BitS
  Not  :: Exp BitS -> Exp BitS
  VarK :: Int -> Exp KeyS
  PRG0 :: Exp KeyS -> Exp KeyS
  PRG1 :: Exp KeyS -> Exp KeyS
  Pair :: Exp a -> Exp b -> Exp (a :*: b)
  Perm :: Exp BitS -> Exp a -> Exp a -> Exp (a :*: a)
  Enc  :: Exp KeyS -> Exp s -> Exp (EncS s)
  Eps  :: Exp EmptyS

data Pat (s :: Shape) where
  PBit  :: Exp BitS -> Pat BitS
  PKey  :: Exp KeyS -> Pat KeyS
  PPair ::             Pat a -> Pat b -> Pat (a :*: b)
  PPerm :: Exp BitS -> Pat a -> Pat a -> Pat (a :*: a)
  PEnc  :: Exp KeyS -> Pat s    -> Pat (EncS s)
  PHide :: Exp KeyS -> Hidden s -> Pat (EncS s)
  PEps  :: Pat EmptyS

data Hidden (s :: Shape) = Hidden
  deriving Eq

-- Syntactic equality
instance Eq (Exp s) where
  (Bit b0)    == (Bit b1)    = (b0 == b1)
  (VarB i)    == (VarB j)    = i == j
  (Not e0)    == (Not e1)    = (e0 == e1)
  (Bit  _)    == _           = False
  (VarB _)    == _           = False
  (Not  _)    == _           = False
  (VarK i)    == (VarK j)    = i == j
  (PRG0 k)    == (PRG0 h)    = (k == h)
  (PRG1 k)    == (PRG1 h)    = (k == h)
  (VarK _)    == _           = False
  (PRG0 _)    == _           = False
  (PRG1 _)    == _           = False
  (Pair x y)  == (Pair u v)  = (x == u) && (y == v)
  (Enc k0 m0) == (Enc k1 m1) = (k0 == k1) && (m0 == m1)
  (Perm b x y) == (Perm d u v) = (b == d) && (x == u) && (y == v)
  Eps == Eps = True
  e == f = f == e

instance Eq (Pat s) where
  (PBit e) == (PBit f) = e == f
  (PKey e) == (PKey f) = e == f
  (PPair a b) == (PPair a' b') = (a == a') && (b == b')
  (PPerm b e f) == (PPerm b' e' f') = (b == b') && (e == e') && (f == f')
  (PEnc  k e) == (PEnc  k' e') = (k == k') && (e == e')
  (PHide k h) == (PHide k' h') = (k == k') && (h == h')
  PEps == PEps = True

-- Some utility functions
xor :: Exp BitS -> Exp BitS -> Bool
xor (Bit b0) (Bit b1) = b0 /= b1
xor (VarB i) (VarB j) = if i == j then False else undefined
xor (Not e0) e1       = not (e0 `xor` e1)
xor e0 (Not e1)       = not (e0 `xor` e1)

proj :: Exp (a :*: a) -> Exp BitS -> Exp a
proj (Perm b e0 e1) b'   = if b `xor` b' then e1 else e0
proj (Pair e0 e1) (Bit False) = e0
proj (Pair e0 e1) (Bit True)  = e1

pair_fst :: Exp (a :*: b) -> Exp a
pair_fst (Pair x _) = x

pair_snd :: Exp (a :*: b) -> Exp b
pair_snd (Pair _ y) = y

dec :: Exp KeyS -> Exp (EncS s) -> Exp s
dec k' (Enc k x) = if k == k' then x else undefined

-- k < k', ie proper yield
yields :: Exp KeyS -> Exp KeyS -> Bool
yields k (PRG0 k') =
  if k == k' then True
  else case k' of
    (VarK _)   -> False
    (PRG0 k'') -> yields k k''
    (PRG1 k'') -> yields k k''
yields k (PRG1 k') =
  if k == k' then True
  else case k' of
    (VarK _)   -> False
    (PRG0 k'') -> yields k k''
    (PRG1 k'') -> yields k k''
yields _ _ = False

-- Convert an expression to a pattern, no normalization/reduction
expToPat :: Exp s -> Pat s
expToPat (Bit b)  = PBit (Bit b)
expToPat (VarB i) = PBit (VarB i)
expToPat (Not e)  = PBit (Not e)
expToPat (VarK i) = PKey (VarK i)
expToPat (PRG0 k) = PKey (PRG0 k)
expToPat (PRG1 k) = PKey (PRG1 k)
expToPat (Pair a b) = PPair (expToPat a) (expToPat b)
expToPat (Perm b e f) = PPerm b (expToPat e) (expToPat f)
expToPat (Enc k e)  = PEnc k (expToPat e)
expToPat Eps = PEps

-- Implementing bit and key renamings
instance Hashable (Exp s) where
  hashWithSalt salt (Bit True)  = Hashable.hashWithSalt salt (0 :: Int)
  hashWithSalt salt (Bit False) = Hashable.hashWithSalt salt (1 :: Int)
  hashWithSalt salt (VarB i) = Hashable.hashWithSalt salt (2*i+2)
  hashWithSalt salt (Not e)  = (Hashable.hashWithSalt salt e) + 2^(5 :: Int)
  hashWithSalt salt (VarK i) = Hashable.hashWithSalt salt (2*i+3)
  hashWithSalt salt (PRG0 k) = (Hashable.hashWithSalt salt k) + (2^(10 :: Int))
  hashWithSalt salt (PRG1 k) = (Hashable.hashWithSalt salt k) + (2^(20 :: Int))
  -- For now we only define hash for bit and key expressions

instance Hashable (Pat s) where
  hashWithSalt salt (PBit e) = Hashable.hashWithSalt salt e
  hashWithSalt salt (PKey e) = Hashable.hashWithSalt salt e

type BitRenaming = HashMap (Exp BitS) (Exp BitS)
type KeyRenaming = HashMap (Exp KeyS) (Exp KeyS)

-- Wrapper for all data structures that can derive pattern
class Patternable a where
  -- The Pattern function, ie p(e, Fix(F_e))
  pattern      :: a -> a
  pattern e = pp e (fst (finalRecoverableKeys e))

  -- Keys
  keys         :: a -> HashSet (Exp KeyS)

  -- Keys \cap Parts
  keysInParts  :: a -> HashSet (Exp KeyS)

  -- The roots of recoverable keys from a pattern e, ie, Root(r(e))
  pr :: a -> HashSet (Exp KeyS)
  pr e = HashSet.filter (\k -> isRecoverable k kset kp) ks where
    ks = keys e
    kp = keysInParts e
    kset = HashSet.foldl' addToKeySet IntMap.empty ks
    -- Use KeySet
  
  -- Recoverable pattern given a set of keys
  pp  :: a -> HashSet (Exp KeyS) -> a

  -- Key recovery operator, ie F_e(S) = r(p(e,S))
  recoveryKeys :: a -> HashSet (Exp KeyS) -> HashSet (Exp KeyS)
  recoveryKeys e ks = pr (pp e ks)
  -- This default impl actually computes Root(r(p(e,S))), but note that
  -- the roots are monotonically decreasing wrt to set inclusion

  -- Normalization
  norm :: a -> a

  -- bit and key renamings
  renameBit :: a -> BitRenaming -> a
  renameKey :: a -> KeyRenaming -> a

-- Packed data structure for keys
data KeyRep = KeyRep {
  root :: Int,                  -- Index of root
  act  :: Maybe Int,            -- word that derives the key from the root
  len  :: Int                   -- length of the word
  } deriving (Eq,Show)
-- Note that:
-- act == Nothing iff the key is atomic
-- act == (Just w) => w < 2^l

instance Hashable (KeyRep) where
  hashWithSalt salt (KeyRep r a l) =
    let h = case a of
          Nothing  -> 0
          (Just w) -> (2^l+w)
    in Hashable.hashWithSalt salt (r*(2^10) + h)
       -- Assume there are no more than 2^10 derived keys for a root, ie, depth(circuit)<2^10

-- Convert a key expression to its packed representation
keyToRep :: Exp KeyS -> KeyRep
keyToRep (VarK i) = KeyRep i Nothing 0
keyToRep (PRG0 k) = KeyRep i r' l' where
  (KeyRep i r l) = keyToRep k
  r' = case r of
    Nothing  -> Just 0
    (Just w) -> Just w
  l' = l+1
keyToRep (PRG1 k) = KeyRep i r' l' where
  (KeyRep i r l) = keyToRep k
  r' = case r of
    Nothing  -> Just 1
    (Just w) -> Just ((Bits.shift 1 l) + w)
  l' = l+1

-- Check if kr0 < kr1, for KeyRep
yield' :: KeyRep -> KeyRep -> Bool
yield' (KeyRep r0 a0 l0) (KeyRep r1 a1 l1) =
  if (r0 == r1) && (l0 < l1) then -- Could be a derived key
    case a0 of
      Nothing   -> True           -- kr0 is atomic
      (Just x0) ->
        case a1 of
          Nothing   -> error "ill-formed key"
          (Just x1) -> let y = (Bits.xor x0 x1)
                           m = (Bits.shift 1 l0)
                       in (y `mod` m == 0)
  else False

type KeySet = IntMap.IntMap (HashSet KeyRep)

-- For now we only need to insert all keys into a KeySet in one pass
addToKeySet :: KeySet -> (Exp KeyS) -> KeySet
addToKeySet kset k =
  let (KeyRep r a l) = keyToRep k
      setOfR  = IntMap.lookup r kset
      setOfR' = case setOfR of
        Nothing  -> HashSet.singleton (KeyRep r a l)
        (Just s) -> HashSet.insert (KeyRep r a l) s
  in IntMap.alter (\_ -> (Just setOfR')) r kset

-- Check if a key yield any other key in a key set
hasDerived :: KeySet -> (Exp KeyS) -> Bool
hasDerived kset k =
  let (KeyRep r a l) = keyToRep k
      setOfR  = IntMap.lookup r kset
      f False k' = if (KeyRep r a l) `yield'` k' then True else False
      f True  _  = True
  in case setOfR of
    Nothing  -> False
    (Just s) -> HashSet.foldl' f False s
    
-- Check if k \in Root(r(e))
isRecoverable :: Exp KeyS -> KeySet -> HashSet (Exp KeyS) -> Bool
isRecoverable k kset kp =
  (HashSet.member k kp) || (hasDerived kset k)

-- The greatest fixed point of F_e
finalRecoverableKeys :: Patternable a => a -> (HashSet (Exp KeyS), Int)
finalRecoverableKeys e = gfix (ks,0) where
  ks = keys e
  gfix :: (HashSet (Exp KeyS),Int) -> (HashSet (Exp KeyS), Int)
  gfix (ks',i) = let ks'' = recoveryKeys e ks'
                 in if (HashSet.size ks'') >= (HashSet.size ks') then (ks',i)
                    else gfix (ks'',i+1)


-- Patternable definition for Pat
instance Patternable (Pat s) where
  keys (PBit b) = HashSet.empty
  keys (PKey k) = HashSet.singleton k
  keys (PPair a b) = HashSet.union (keys a) (keys b)
  keys (PPerm b e f) = HashSet.union (keys e) (keys f)
  keys (PEnc  k e) = HashSet.union (HashSet.singleton k) (keys e)
  keys (PHide k s) = HashSet.singleton k
  keys PEps = HashSet.empty

  keysInParts (PBit b) = HashSet.empty
  keysInParts (PKey k) = HashSet.singleton k
  keysInParts (PPair a b) = HashSet.union (keysInParts a) (keysInParts b)
  keysInParts (PPerm b e f) = HashSet.union (keysInParts e) (keysInParts f)
  keysInParts (PEnc  k e) = keysInParts e
  keysInParts (PHide k s) = HashSet.empty
  keysInParts PEps = HashSet.empty

  pp (PPair e f) ks = PPair (pp e ks) (pp f ks)
  pp (PPerm b e f) ks = PPerm b (pp e ks) (pp f ks)
  pp (PEnc k e) ks =
    if (HashSet.member k ks)
    then PEnc  k (pp e ks)
    else PHide k Hidden
  pp (PHide k h) ks = PHide k h
  pp e _ = e

  norm (PBit e) = PBit (normalizeBit e)
  norm (PKey e) = PKey (normalizeKey e)
  norm (PPair p q) = PPair (norm p) (norm q)
  norm (PPerm b p q) =
    let p' = norm p
        q' = norm q
    in normalizePerm (PPerm b p' q')
  norm (PEnc  k m) = PEnc  (normalizeKey k) (norm m)
  norm (PHide k h) = PHide (normalizeKey k) h

  renameBit (PBit e) hm = PBit (applyBitRenaming e hm)
  renameBit (PKey e) hm = PKey e
  renameBit (PPair e f) hm = PPair (renameBit e hm) (renameBit f hm)
  renameBit (PPerm b e f) hm = PPerm b' (renameBit e hm) (renameBit f hm) where
    b' = case HashMap.lookup b hm of
      Nothing    -> b
      (Just b'') -> b''
  renameBit (PEnc k e) hm = PEnc k (renameBit e hm)
  renameBit e _ = e             -- Both PHide and PEps

  renameKey (PBit e) hm = PBit e
  renameKey (PKey e) hm = PKey (applyKeyRenaming e hm)
  renameKey (PPair e f) hm = PPair (renameKey e hm) (renameKey f hm)
  renameKey (PPerm b e f) hm = PPerm b (renameKey e hm) (renameKey f hm)
  renameKey (PEnc k e) hm = PEnc (applyKeyRenaming k hm) (renameKey e hm)
  renameKey (PHide k h) hm = PHide (applyKeyRenaming k hm) h
  renameKey e _ = e             -- PEps

-- apply bit renaming to bit expressions
applyBitRenaming :: Exp BitS -> BitRenaming -> Exp BitS
applyBitRenaming (Bit b) _   = Bit b
applyBitRenaming (VarB i) hm =
  case HashMap.lookup (VarB i) hm of
    Nothing   -> VarB i
    (Just e') -> e'
applyBitRenaming (Not e) hm =
  case HashMap.lookup (Not e) hm of
    Nothing   -> (Not (applyBitRenaming e hm))
    (Just e') -> e'

-- apply key renaming to key expressions
applyKeyRenaming :: Exp KeyS -> KeyRenaming -> Exp KeyS
applyKeyRenaming k hm =
  case HashMap.lookup k hm of
    (Just e') -> e'
    Nothing   -> case k of
      (VarK i) -> VarK i
      (PRG0 e) -> PRG0 (applyKeyRenaming e hm)
      (PRG1 e) -> PRG1 (applyKeyRenaming e hm)

-- normalization
normalizeBit :: Exp BitS -> Exp BitS
normalizeBit (Bit  b) = Bit  b
normalizeBit (VarB i) = VarB i  -- Maybe also normalize index
normalizeBit (Not (Bit True))  = Bit False
normalizeBit (Not (Bit False)) = Bit True
normalizeBit (Not (Not e))     = normalizeBit e
normalizeBit (Not e)           = Not e

normalizeKey :: Exp KeyS -> Exp KeyS
normalizeKey = id               -- Maybe also normalize index

normalizePerm :: Pat (a :*: a) -> Pat (a :*: a)
normalizePerm (PPerm b p q) = case b of
  (Bit True)  -> PPair p q
  (Bit False) -> PPair q p
  (Not b')    -> normalizePerm (PPerm b' q p)
  (VarB i)    -> PPerm b p q
normalizePerm (PPair p q) = PPair p q

{- Expression and pattern display -}
instance Show (Hidden s) where
  show Hidden = "*"

instance Show (Exp s) where
  show (Bit b)  = show b
  show (VarB i) = "B"++ (show i)
  show (Not e)  = "~(" ++ (show e) ++ ")"
  show (VarK i) = "K"++ (show i)
  show (PRG0 k) = "G0("++ (show k) ++ ")"
  show (PRG1 k) = "G1("++ (show k) ++ ")"
  show (Pair a b) = "P(" ++ (show a) ++ "," ++ (show b) ++ ")"
  show (Perm b e f) = "Pm[" ++ (show b) ++ "](" ++ (show e) ++ "," ++ (show f) ++ ")"
  show (Enc  k e) = "E[" ++ (show k) ++ "](" ++ (show e) ++ ")"
  show Eps = "ε"

instance Show (Pat s) where
  show (PBit e) = "#" ++ (show e)
  show (PKey e) = "#" ++ (show e)
  show (PPair p q) = "#P(" ++ (show p) ++ "," ++ (show q) ++ ")"
  show (PPerm b p q) = "#Pm[" ++ (show b) ++ "](" ++ (show p) ++ "," ++ (show q) ++ ")"
  show (PEnc  k e) = "#E[" ++ (show k) ++ "](" ++ (show e) ++ ")"
  show (PHide k e) = "#H[" ++ (show k) ++ "](" ++ (show e) ++ ")"
  show PEps = "ε"
  
