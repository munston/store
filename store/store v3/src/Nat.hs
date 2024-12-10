
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies , FlexibleContexts #-}
{-# LANGUAGE TypeOperators , TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Nat where

data Nat = S Nat | Z

-- Type-level modulo function
type family Mod (x :: Nat) (y :: Nat) :: Nat where
  Mod Z y = Z
  Mod x (S Z) = Z  -- Modulo by 1 is always 0
  Mod x y = IfLt x y x (Mod (Subtract x y) y)

-- Helper to check if x < y
type family IfLt (x :: Nat) (y :: Nat) (t :: Nat) (f :: Nat) :: Nat where
  IfLt Z Z t f = f
  IfLt Z (S y) t f = t
  IfLt (S x) Z t f = f
  IfLt (S x) (S y) t f = IfLt x y t f

-- Type-level addition
type family Plus (x :: Nat) (y :: Nat) :: Nat where
  Plus Z y = y
  Plus (S x) y = S (Plus x y)

-- Subtraction at the type level
type family Subtract (x :: Nat) (y :: Nat) :: Nat where
  Subtract Z y = Z
  Subtract x Z = x
  Subtract (S x) (S y) = Subtract x y

-- Value-level conversion for Nat
class FromNat (n :: Nat) where
  fromNat :: Int

instance FromNat Z where
  fromNat = 0

instance FromNat n => FromNat (S n) where
  fromNat = 1 + fromNat @n

-- Example of testing Mod at the value level
modValue :: forall x y. (FromNat (Mod x y)) => Int
modValue = fromNat @(Mod x y)

-- Testing Mod at the value level
test :: Int
test = modValue @(S (S (S Z))) @(S (S Z)) -- Computes 3 `mod` 2, should return 1