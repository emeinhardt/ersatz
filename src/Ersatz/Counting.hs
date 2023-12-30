{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
-- |

module Ersatz.Counting where

import Ersatz.Bits
import Ersatz.Codec
import Ersatz.Equatable
import Ersatz.Orderable

class Countable t where
  exactly :: Int -> [ t ] -> t
  atmost  :: Int -> [ t ] -> t
  atleast :: Int -> [ t ] -> t

instance (Orderable (Bits b) b, HasBits b b, Codec b, Decoded b ~ Bool) => Countable b where
  exactly k bs = encode (fromIntegral k) === sumBit bs

  atmost k bs = encode (fromIntegral k) >=? (sumBits @[] @b @b) bs

  atleast k bs = encode (fromIntegral k) <=? (sumBits @[] @b @b) bs

