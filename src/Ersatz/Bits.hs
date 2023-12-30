{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
--------------------------------------------------------------------
-- |
-- Copyright :  © Edward Kmett 2010-2015, © Eric Mertens 2014, Johan Kiviniemi 2013
-- License   :  BSD3
-- Maintainer:  Edward Kmett <ekmett@gmail.com>
-- Stability :  experimental
-- Portability: non-portable
--
-- 'Bit1' .. 'Bit8' represent fixed length bit vectors.
-- The most significant bit comes first.
-- 'Bit1' and 'Bit2' have modular arithmetic
-- (the result has the same width as the arguments, overflow is ignored).
--
-- 'Bits' is an arbitrary length natural number type.
-- The least significant bit comes first.
-- 'Bits' has full arithmetic
-- (the result has large enough width so that there is no overflow).


--------------------------------------------------------------------
module Ersatz.Bits
  (
  -- * Fixed length bit vectors
    Bit1(..), Bit2(..), Bit3(..), Bit4(..), Bit5(..), Bit6(..), Bit7(..), Bit8(..)
  -- * Variable length bit vectors
  , Bits(Bits)
  , HasBits(..)
  , isEven
  , isOdd
  , sumBit
  , sumBits
  -- * Adders
  , fullAdder, halfAdder
  ) where

import Control.Applicative
import Control.Monad.Trans.State (State, runState, get, put, StateT)
import Data.Bits ((.&.), (.|.), shiftL, shiftR)
import qualified Data.Bits as Data
import Data.Foldable (toList)
import Data.Functor.Identity (Identity)
import Data.List (unfoldr, foldl')
import Data.Stream.Infinite (Stream(..))
import Data.Word (Word8)
import Ersatz.Bit
import Ersatz.Codec
import Ersatz.Equatable
import Ersatz.Orderable
import Ersatz.Variable
import GHC.Generics
import Prelude hiding (and, or, not, (&&), (||))

-- | A container of 1 'Bit' that 'encode's from and 'decode's to 'Word8'.
newtype Bit1 b = Bit1 b deriving (Show,Generic)
-- | A container of 2 'Bit's that 'encode's from and 'decode's to 'Word8'. MSB is first.
data Bit2 b = Bit2 !b !b deriving (Show,Generic)
-- | A container of 3 'Bit's that 'encode's from and 'decode's to 'Word8'. MSB is first.
data Bit3 b = Bit3 !b !b !b deriving (Show,Generic)
-- | A container of 4 'Bit's that 'encode's from and 'decode's to 'Word8'. MSB is first.
data Bit4 b = Bit4 !b !b !b !b deriving (Show,Generic)
-- | A container of 5 'Bit's that 'encode's from and 'decode's to 'Word8'. MSB is first.
data Bit5 b = Bit5 !b !b !b !b !b deriving (Show,Generic)
-- | A container of 6 'Bit's that 'encode's from and 'decode's to 'Word8'. MSB is first.
data Bit6 b = Bit6 !b !b !b !b !b !b deriving (Show,Generic)
-- | A container of 7 'Bit's that 'encode's from and 'decode's to 'Word8'. MSB is first.
data Bit7 b = Bit7 !b !b !b !b !b !b !b deriving (Show,Generic)
-- | A container of 8 'Bit's that 'encode's from and 'decode's to 'Word8'. MSB is first.
data Bit8 b = Bit8 !b !b !b !b !b !b !b !b deriving (Show,Generic)

instance (Boolean b) => Boolean (Bit1 b)
instance (Boolean b) => Boolean (Bit2 b)
instance (Boolean b) => Boolean (Bit3 b)
instance (Boolean b) => Boolean (Bit4 b)
instance (Boolean b) => Boolean (Bit5 b)
instance (Boolean b) => Boolean (Bit6 b)
instance (Boolean b) => Boolean (Bit7 b)
instance (Boolean b) => Boolean (Bit8 b)

instance (Equatable b τ) => Equatable (Bit1 b) τ
instance (Equatable b τ) => Equatable (Bit2 b) τ
instance (Equatable b τ) => Equatable (Bit3 b) τ
instance (Equatable b τ) => Equatable (Bit4 b) τ
instance (Equatable b τ) => Equatable (Bit5 b) τ
instance (Equatable b τ) => Equatable (Bit6 b) τ
instance (Equatable b τ) => Equatable (Bit7 b) τ
instance (Equatable b τ) => Equatable (Bit8 b) τ

instance Orderable b τ => Orderable (Bit1 b) τ
instance Orderable b τ => Orderable (Bit2 b) τ
instance Orderable b τ => Orderable (Bit3 b) τ
instance Orderable b τ => Orderable (Bit4 b) τ
instance Orderable b τ => Orderable (Bit5 b) τ
instance Orderable b τ => Orderable (Bit6 b) τ
instance Orderable b τ => Orderable (Bit7 b) τ
instance Orderable b τ => Orderable (Bit8 b) τ

instance Variable b => Variable (Bit1 b)
instance Variable b => Variable (Bit2 b)
instance Variable b => Variable (Bit3 b)
instance Variable b => Variable (Bit4 b)
instance Variable b => Variable (Bit5 b)
instance Variable b => Variable (Bit6 b)
instance Variable b => Variable (Bit7 b)
instance Variable b => Variable (Bit8 b)

instance Codec (Bit1 Bit) where
  type Decoded (Bit1 Bit) = Word8
  decode s (Bit1 a) = boolsToNum1 <$> decode s a
  encode i = Bit1 a where (a:>_) = bitsOf i

instance Codec (Bit2 Bit) where
  type Decoded (Bit2 Bit) = Word8
  decode s (Bit2 a b) = boolsToNum2 <$> decode s a <*> decode s b
  encode i = Bit2 a b where (b:>a:>_) = bitsOf i

instance Codec (Bit3 Bit) where
  type Decoded (Bit3 Bit) = Word8
  decode s (Bit3 a b c) = boolsToNum3 <$> decode s a <*> decode s b <*> decode s c
  encode i = Bit3 a b c where (c:>b:>a:>_) = bitsOf i

instance Codec (Bit4 Bit) where
  type Decoded (Bit4 Bit) = Word8
  decode s (Bit4 a b c d) = boolsToNum4 <$> decode s a <*> decode s b <*> decode s c <*> decode s d
  encode i = Bit4 a b c d where (d:>c:>b:>a:>_) = bitsOf i

instance Codec (Bit5 Bit) where
  type Decoded (Bit5 Bit) = Word8
  decode s (Bit5 a b c d e) = boolsToNum5 <$> decode s a <*> decode s b <*> decode s c <*> decode s d <*> decode s e
  encode i = Bit5 a b c d e where (e:>d:>c:>b:>a:>_) = bitsOf i

instance Codec (Bit6 Bit) where
  type Decoded (Bit6 Bit) = Word8
  decode s (Bit6 a b c d e f) = boolsToNum6 <$> decode s a <*> decode s b <*> decode s c <*> decode s d <*> decode s e <*> decode s f
  encode i = Bit6 a b c d e f where (f:>e:>d:>c:>b:>a:>_) = bitsOf i

instance Codec (Bit7 Bit) where
  type Decoded (Bit7 Bit) = Word8
  decode s (Bit7 a b c d e f g) = boolsToNum7 <$> decode s a <*> decode s b <*> decode s c <*> decode s d <*> decode s e <*> decode s f <*> decode s g
  encode i = Bit7 a b c d e f g where (g:>f:>e:>d:>c:>b:>a:>_) = bitsOf i

instance Codec (Bit8 Bit) where
  type Decoded (Bit8 Bit) = Word8
  decode s (Bit8 a b c d e f g h) = boolsToNum8 <$> decode s a <*> decode s b <*> decode s c <*> decode s d <*> decode s e <*> decode s f <*> decode s g <*> decode s h
  encode i = Bit8 a b c d e f g h where (h:>g:>f:>e:>d:>c:>b:>a:>_) = bitsOf i

instance Codec (Bit1 Bool) where
  type Decoded (Bit1 Bool) = Word8
  decode _ (Bit1 a) = Just $ boolsToNum1 a
  encode i = Bit1 a where (a:>_) = bitsOf i

instance Codec (Bit2 Bool) where
  type Decoded (Bit2 Bool) = Word8
  decode _ (Bit2 a b) = Just $ boolsToNum2 a b
  encode i = Bit2 a b where (b:>a:>_) = bitsOf i

instance Codec (Bit3 Bool) where
  type Decoded (Bit3 Bool) = Word8
  decode _ (Bit3 a b c) = Just $ boolsToNum3 a b c
  encode i = Bit3 a b c where (c:>b:>a:>_) = bitsOf i

instance Codec (Bit4 Bool) where
  type Decoded (Bit4 Bool) = Word8
  decode _ (Bit4 a b c d) = Just $ boolsToNum4 a b c d
  encode i = Bit4 a b c d where (d:>c:>b:>a:>_) = bitsOf i

instance Codec (Bit5 Bool) where
  type Decoded (Bit5 Bool) = Word8
  decode _ (Bit5 a b c d e) = Just $ boolsToNum5 a b c d e
  encode i = Bit5 a b c d e where (e:>d:>c:>b:>a:>_) = bitsOf i

instance Codec (Bit6 Bool) where
  type Decoded (Bit6 Bool) = Word8
  decode _ (Bit6 a b c d e f) = Just $ boolsToNum6 a b c d e f
  encode i = Bit6 a b c d e f where (f:>e:>d:>c:>b:>a:>_) = bitsOf i

instance Codec (Bit7 Bool) where
  type Decoded (Bit7 Bool) = Word8
  decode _ (Bit7 a b c d e f g) = Just $ boolsToNum7 a b c d e f g
  encode i = Bit7 a b c d e f g where (g:>f:>e:>d:>c:>b:>a:>_) = bitsOf i

instance Codec (Bit8 Bool) where
  type Decoded (Bit8 Bool) = Word8
  decode _ (Bit8 a b c d e f g h) = Just $ boolsToNum8 a b c d e f g h
  encode i = Bit8 a b c d e f g h where (h:>g:>f:>e:>d:>c:>b:>a:>_) = bitsOf i

boolsToNum1 :: Bool -> Word8
boolsToNum1 = boolToNum

boolsToNum2 :: Bool -> Bool -> Word8
boolsToNum2 a b = boolsToNum [a,b]

boolsToNum3 :: Bool -> Bool -> Bool -> Word8
boolsToNum3 a b c = boolsToNum [a,b,c]

boolsToNum4 :: Bool -> Bool -> Bool -> Bool -> Word8
boolsToNum4 a b c d = boolsToNum [a,b,c,d]

boolsToNum5 :: Bool -> Bool -> Bool -> Bool -> Bool -> Word8
boolsToNum5 a b c d e = boolsToNum [a,b,c,d,e]

boolsToNum6 :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Word8
boolsToNum6 a b c d e f = boolsToNum [a,b,c,d,e,f]

boolsToNum7 :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Word8
boolsToNum7 a b c d e f g = boolsToNum [a,b,c,d,e,f,g]

boolsToNum8 :: Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Word8
boolsToNum8 a b c d e f g h = boolsToNum [a,b,c,d,e,f,g,h]

bitsOf :: (Num a, Data.Bits a, Boolean b) => a -> Stream b
bitsOf n = bool (numToBool (n .&. 1)) :> bitsOf (n `shiftR` 1)
{-# INLINE bitsOf #-}

numToBool :: (Eq a, Num a) => a -> Bool
numToBool 0 = False
numToBool _ = True
{-# INLINE numToBool #-}

boolsToNum :: (Num a, Data.Bits a) => [Bool] -> a
boolsToNum = foldl' (\n a -> (n `shiftL` 1) .|. boolToNum a) 0
{-# INLINE boolsToNum #-}

boolToNum :: Num a => Bool -> a
boolToNum False = 0
boolToNum True  = 1
{-# INLINE boolToNum #-}


-- | This instance provides modular arithmetic (overflow is ignored).
instance (Boolean b) => Num (Bit1 b) where
  Bit1 a + Bit1 b = Bit1 (xor a b)
  Bit1 a * Bit1 b = Bit1 (a && b)
  Bit1 a - Bit1 b = Bit1 (xor a b)
  negate a = a
  abs a    = a
  signum a = a
  fromInteger = Bit1 . bool . odd

-- | Compute the sum and carry bit from adding three bits.
-- fullAdder :: Bit -> Bit -> Bit -> (Bit, Bit) -- ^ (sum, carry)
fullAdder :: (Boolean b) => b -> b -> b -> (b, b) -- ^ (sum, carry)
fullAdder a b c =
  -- ( full_Adder_Sum a b c , full_Adder_Carry a b c )
  let (s1,c1) = halfAdder a b ; (s2,c2) = halfAdder s1 c in (s2, c1||c2)
  -- following does not work (formula generation does not stop), why?
  {-
  ( Run $ exists >>= \ x -> do
      assert (     a ||     b ||     c || not x ) ; assert ( not a || not b || not c || x )
      assert (     a || not b || not c || not x ) ; assert ( not a ||     b ||     c || x )
      assert ( not a ||     b || not c || not x ) ; assert (     a || not b ||     c || x )
      assert ( not a || not b ||     c || not x ) ; assert (     a ||     b || not c || x )
      return x
  , Run $ exists >>= \ x -> do
      assert ( not b || not c || x ) ; assert ( b || c || not x )
      assert ( not a || not c || x ) ; assert ( a || c || not x )
      assert ( not a || not b || x ) ; assert ( a || b || not x )
      return x
  )
  -}

-- | Compute the sum and carry bit from adding two bits.
halfAdder :: (Boolean b) => b -> b -> (b, b) -- ^ (sum, carry)
halfAdder a b = (a `xor` b, a && b)

-- | This instance provides modular arithmetic (overflow is ignored).
instance (Boolean b) => Num (Bit2 b) where
  Bit2 a2 a1 + Bit2 b2 b1 = Bit2 s2 s1 where
    (s1,c2) = halfAdder a1 b1
    (s2,_)  = fullAdder a2 b2 c2
  Bit2 a2 a1 * Bit2 b2 b1 = Bit2 ((a1 && b2) `xor` (a2 && b1)) (a1 && b1)
    -- wallace tree
    --
    --   XX
    --  XX
    -- ----
    --  XXX
    --  X
    -- ----
    -- XXXX
    --
    -- But we only need the first 2 bits
  negate (Bit2 a b) = Bit2 (not a) (not b) + 1
  abs a = a
  signum (Bit2 a b) = Bit2 false (a || b)
  fromInteger k = Bit2 (bool (k .&. 2 /= 0)) (bool (k .&. 1 /= 0))

-- | A container of 'Bit's that is suitable for comparisons and arithmetic. Bits are stored
-- with least significant bit first to enable phantom 'false' values
-- to be truncated.
newtype Bits b = Bits { _getBits :: [b] }

instance (Show b) => Show (Bits b) where
  showsPrec d (Bits xs) = showParen (d > 10) $
    showString "Bits " . showsPrec 11 xs

instance (Boolean b, Equatable b Bit) => Equatable (Bits b) Bit where
  Bits xs === Bits ys = and (zipWithBits (===) xs ys)
  Bits xs /== Bits ys = or  (zipWithBits (/==) xs ys)

-- | Zip the component bits of a 'Bits' extending the
-- shorter argument with 'false' values.
zipWithBits :: (Boolean b) => (b -> b -> a) -> [b] -> [b] -> [a]
zipWithBits _ []     []     = []
zipWithBits f (x:xs) (y:ys) = f x y : zipWithBits f xs ys
zipWithBits f xs     []     = map (`f` false) xs
zipWithBits f []     ys     = map (false `f`) ys

instance (Boolean b, Orderable b Bit) => Orderable (Bits b) Bit where
  Bits xs <?  Bits ys = orderHelper false xs ys
  Bits xs <=? Bits ys = orderHelper true  xs ys

orderHelper :: (Boolean b, Orderable b τ) => τ -> [b] -> [b] -> τ -- not possible becuase of a lack of relevant Orderable instances
orderHelper c0 xs ys = foldl aux c0 (zipWithBits (,) xs ys)
    where
    aux c (x,y) = c && x === y || x <? y

instance (Codec b, Boolean b, Decoded b ~ Bool) => Codec (Bits b) where
  type Decoded (Bits b) = Integer

  decode s (Bits xs) =
    do ys <- traverse (decode s) xs
       -- bools to Integers
       let zs = map (\x -> if x then 1 else 0) ys
       -- Integers to Integer
       return (foldr (\x acc -> x + 2 * acc) 0 zs)

  encode = Bits . unfoldr step
    where
    step x =
      case compare x 0 of
        LT -> error "Bits/encode: Negative number"
        EQ -> Nothing
        GT -> Just (if odd x then true else false, x `div` 2)

unbits :: HasBits a b => a -> [b]
unbits a = case bits a of Bits xs -> xs

-- | Add two 'Bits' values given an incoming carry bit.
addBits :: (HasBits a τ, HasBits b τ, Boolean τ) => τ -> a -> b -> Bits τ
addBits c xs0 ys0 = Bits (add2 c (unbits xs0) (unbits ys0)) where
  add2 cin []     ys    = add1 cin ys
  add2 cin xs     []    = add1 cin xs
  add2 cin (x:xs) (y:ys)= s : add2 cout xs ys where
    (s,cout)            = fullAdder x y cin

  add1 cin []           = [cin]
  add1 cin (x:xs)       = s : add1 cout xs where
    (s,cout)            = halfAdder cin x

-- | Compute the sum of a source of 'Bits' values.
sumBits :: (Foldable t, HasBits a τ, Boolean τ) => t a -> Bits τ
sumBits = sumBits' . map bits . toList

sumBits' :: Boolean τ => [Bits τ] -> Bits τ
sumBits' []  = Bits []
sumBits' [x] = x
sumBits' xs0 = sumBits (merge xs0) where
  merge [x] = [x]
  merge []  = []
  merge (x1:x2:xs) = addBits false x1 x2 : merge xs

-- | Optimization of 'sumBits' enabled when summing
-- individual 'Bit's.
sumBit :: forall t b. (Boolean b, Foldable t, HasBits b b) => t b -> Bits b
sumBit t =
  case runState (merge (map bits h2)) h1 of
    (s,[]) -> s
    _      -> error "Bits.betterSumBits: OOPS! Bad algorithm!"

  where
  ts = toList t
  (h1,h2) = splitAt ((length ts-1) `div` 2) ts

  spareBit :: StateT [b] Identity b
  spareBit = do
    xs <- get
    case xs of
      []   -> return false
      y:ys -> put ys >> return y

  merge :: [Bits b] -> State [b] (Bits b)
  merge [x] = return x
  merge []  = return (Bits [])
  merge xs  = merge =<< merge' xs

  merge' :: [Bits b] -> State [b] [Bits b]
  merge' []  = return []
  merge' [x] = return [x]
  merge' (x1:x2:xs) =
    do cin <- spareBit
       xs' <- merge' xs
       return (addBits cin x1 x2 : xs')

-- | Predicate for odd-valued 'Bits's.
isOdd :: (Boolean τ) => HasBits b τ => b -> τ
isOdd b = case unbits b of
  []    -> false
  (x:_) -> x

-- | Predicate for even-valued 'Bits's.
isEven :: (Boolean τ) => HasBits b τ => b -> τ
isEven = not . isOdd

-- | 'HasBits' provides the 'bits' method for embedding
-- fixed with numeric encoding types into the arbitrary width
-- 'Bits' type.
class HasBits a b where
  bits :: a -> Bits b

instance HasBits Bit Bit where
  bits x = Bits [x]

instance HasBits (Bit1 b) b where
  bits (Bit1 x0) = Bits [x0]

instance HasBits (Bit2 b) b where
  bits (Bit2 x1 x0) = Bits [x0,x1]

instance HasBits (Bit3 b) b where
  bits (Bit3 x2 x1 x0) = Bits [x0,x1,x2]

instance HasBits (Bit4 b) b where
  bits (Bit4 x3 x2 x1 x0) = Bits [x0,x1,x2,x3]

instance HasBits (Bit5 b) b where
  bits (Bit5 x4 x3 x2 x1 x0) = Bits [x0,x1,x2,x3,x4]

instance HasBits (Bit6 b) b where
  bits (Bit6 x5 x4 x3 x2 x1 x0) = Bits [x0,x1,x2,x3,x4,x5]

instance HasBits (Bit7 b) b where
  bits (Bit7 x6 x5 x4 x3 x2 x1 x0) = Bits [x0,x1,x2,x3,x4,x5,x6]

instance HasBits (Bit8 b) b where
  bits (Bit8 x7 x6 x5 x4 x3 x2 x1 x0) = Bits [x0,x1,x2,x3,x4,x5,x6,x7]

instance HasBits (Bits b) b where
  bits = id

mulBits :: (Boolean b) => Bits b -> Bits b -> Bits b
mulBits (Bits xs) (Bits ys0)
  = sumBits
  $ zipWith aux xs (iterate times2 ys0)
  where
  times2 = (false:)
  aux x ys = Bits (map (x &&) ys)

-- | This instance provides full arithmetic.
-- The result has large enough width so that there is no overflow.
--
-- Subtraction is modified: @a - b@ denotes @max 0 (a - b)@.
--
-- Width of @a + b@ is @1 + max (width a) (width b)@,
-- width of @a * b@ is @(width a) + (width b)@,
-- width of @a - b@ is @max (width a) (width b)@.
--
-- @fromInteger@ will raise 'error' for negative arguments.
instance (Boolean b, Codec b, Decoded b ~ Bool) => Num (Bits b) where
  (+) = addBits false
  (*) = mulBits
  (-) = subBits
  fromInteger = encode
  signum (Bits xs) = Bits [or xs]
  abs x = x

fullSubtract :: (Boolean b) => b -> b -> b -> (b,b)
fullSubtract c x y =
  (x `xor` y `xor` c, x && y && c || not x && y || not x && c)

subBits :: (Boolean τ, HasBits a τ, HasBits b τ) => a -> b -> Bits τ
subBits xs0 ys0 = Bits (map (not cN &&) ss) where
  (cN, ss) = aux false (unbits xs0) (unbits ys0)

  aux c [] [] = (c, [])
  aux c [] ys = aux c [false] ys
  aux c xs [] = aux c xs      [false]
  aux c (x:xs) (y:ys) = fmap (z :) (aux cout xs ys) where
    (z,cout) = fullSubtract c x y
