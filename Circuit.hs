{-# LANGUAGE GADTs, DataKinds, TypeOperators #-}
{- Inductive circuit representation -}
module Circuit where

data WShape = I | WShape :-: WShape
  deriving Eq

data Circuit a b where
  SWAP    :: Circuit (a :-: b) (b :-: a)
  ASSOC   :: Circuit (a :-: (b :-: c)) ((a :-: b) :-: c)
  UNASSOC :: Circuit ((a :-: b) :-: c) (a :-: (b :-: c))
  CAT     :: Circuit a b -> Circuit b c -> Circuit a c
  FIRST   :: Circuit a b -> Circuit (a :-: c) (b :-: c)
  DUP     :: Circuit I (I :-: I)
  NAND    :: Circuit (I :-: I) I

data Wires a w where
  W :: a -> Wires a I
  (:+:) :: Wires a x -> Wires a y -> Wires a (x :-: y)

-- Evaluating a circuit to a bundle of bits
evalCircuit :: Circuit a b -> Wires Bool a -> Wires Bool b
evalCircuit SWAP (a :+: b) = b :+: a
evalCircuit ASSOC (a :+: (b :+: c)) = (a :+: b) :+: c
evalCircuit UNASSOC ((a :+: b) :+: c) = a :+: (b :+: c)
evalCircuit (CAT c0 c1) x = evalCircuit c1 (evalCircuit c0 x)
evalCircuit (FIRST c) (a :+: b) = (evalCircuit c a) :+: b
evalCircuit DUP x = (x :+: x)
evalCircuit NAND (W x :+: W y) = W (not (x && y))

-- The circuit combinator Second
second :: Circuit a b -> Circuit (c :-: a) (c :-: b)
second c = CAT SWAP (CAT (FIRST c) SWAP)


-- Example: x && y
andCircuit :: Circuit (I :-: I) I
andCircuit =
  let c1 = CAT DUP NAND in
    let c2 = FIRST c1 in
      let c3 = CAT DUP c2 in
        let c4 = CAT c3 NAND in
          let c5 = FIRST c4 in
            let c6 = CAT DUP c5 in
              let c7 = CAT c6 NAND in
                CAT NAND c7
                

{- Display -}
displayWires :: Show a => Wires a x -> String
displayWires (W v) = "W " ++ (show v)
displayWires (w :+: v) = "(" ++ (displayWires w) ++ " :+: " ++ (displayWires v) ++ ")"


instance Show a => Show (Wires a w) where
  show w = displayWires w

instance Eq a => Eq (Wires a w) where
  (W x) == (W y)           = x == y
  (u :+: v) == (u' :+: v') = (u == u') && (v == v')

instance Show (Circuit s t) where
  show SWAP = "SWAP"
  show ASSOC = "ASSOC"
  show UNASSOC = "UNASSOC"
  show DUP = "DUP"
  show NAND = "NAND"
  show (FIRST c) = "(FIRST " ++ (show c) ++ ")"
  show (CAT c0 c1) = "(CAT " ++ (show c0) ++ " " ++ (show c1) ++ ")"
  
