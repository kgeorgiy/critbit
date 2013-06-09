{-# LANGUAGE BangPatterns #-}
-- |
-- Module      :  Data.CritBit.Tree
-- Copyright   :  (c) Bryan O'Sullivan 2013
-- License     :  BSD-style
-- Maintainer  :  bos@serpentine.com
-- Stability   :  experimental
-- Portability :  GHC
--
-- "Core" functions that implement the crit-bit tree algorithms.
--
-- I plopped these functions into their own source file to demonstrate
-- just how small the core of the crit-bit tree concept is.
--
-- I have also commented this module a bit more heavily than I usually
-- do, in the hope that the comments will make the code more
-- approachable to less experienced Haskellers.
module Data.CritBit.Core
    (
    -- * Public functions
      insertWithKey
    , lookupWith
    , updateLookupWithKey
    , leftmost
    , rightmost
    -- * Internal functions
    , calcDirection
    , choose
    , select
    , followPrefixes
    , followPrefixesFrom
    , followPrefixesByteFrom
    , setLeft
    , setRight
    , (.!)
    , findAndReplace
    ) where

import Data.Bits ((.|.), (.&.), complement, shiftR, xor)
import Data.CritBit.Types.Internal
import Data.Word (Word16)

-- | /O(log n)/. Insert with a function, combining key, new value and old value.
-- @'insertWithKey' f key value cb@
-- will insert the pair (key, value) into cb if key does not exist in the map.
-- If the key does exist, the function will insert the pair
-- @(key,f key new_value old_value)@.
-- Note that the key passed to f is the same key passed to insertWithKey.
--
-- > let f key new_value old_value = byteCount key + new_value + old_value
-- > insertWithKey f "a" 1 (fromList [("a",5), ("b",3)]) == fromList [("a",7), ("b",3)]
-- > insertWithKey f "c" 1 (fromList [("a",5), ("b",3)]) == fromList [("a",5), ("b",3), ("c",1)]
-- > insertWithKey f "a" 1 empty                         == singleton "a" 1
insertWithKey :: CritBitKey k => (k -> v -> v -> v) -> k -> v -> CritBit k v
              -> CritBit k v
insertWithKey f k v (CritBit root) = CritBit . go $ root
  where
    go i@(Internal left right _ _) = go $ choose k i left right
    go (Leaf lk _)         = rewalk root
      where
        rewalk i@(Internal left right _ _) =
          select n nob i (finish i)
                         (choose k i (setLeft  i $ rewalk left )
                                     (setRight i $ rewalk right))
        rewalk i = finish i

        finish (Leaf _ v') | k == lk = Leaf k (f k v v')
        finish node
          | nd == 0   = Internal { ileft = node, iright = Leaf k v,
                                   ibyte = n, iotherBits = nob }
          | otherwise = Internal { ileft = Leaf k v, iright = node,
                                   ibyte = n, iotherBits = nob }

        (n, nob, c) = followPrefixes k lk
        nd          = calcDirection nob c
    go Empty = Leaf k v
{-# INLINABLE insertWithKey #-}

lookupWith :: (CritBitKey k) =>
              a                 -- ^ Failure continuation
           -> (v -> a)          -- ^ Success continuation
           -> k
           -> CritBit k v -> a
-- We use continuations here to avoid reimplementing the lookup
-- algorithm with trivial variations.
lookupWith notFound found k (CritBit root) = go root
  where
    go i@(Internal left right _ _) = go $ choose k i left right
    go (Leaf lk v) | k == lk = found v
    go _                     = notFound
{-# INLINE lookupWith #-}

-- | /O(k)/. Lookup and update; see also 'updateWithKey'.
-- This function returns the changed value if it is updated, or
-- the original value if the entry is deleted.
--
-- > let f k x = if x == 5 then Just (x + fromEnum (k < "d")) else Nothing
-- > updateLookupWithKey f "a" (fromList [("b",3), ("a",5)]) == (Just 6, fromList [("a", 6), ("b",3)])
-- > updateLookupWithKey f "c" (fromList [("a",5), ("b",3)]) == (Nothing, fromList [("a",5), ("b",3)])
-- > updateLookupWithKey f "b" (fromList [("a",5), ("b",3)]) == (Just 3, singleton "a" 5)
updateLookupWithKey :: (CritBitKey k) => (k -> v -> Maybe v) -> k
                       -> CritBit k v -> (Maybe v, CritBit k v)
updateLookupWithKey f k t = findAndReplace (Nothing, t) found k t
  where
    found v cont = case f k v of
                     Just v'  -> (Just v', cont $ Leaf k v')
                     Nothing  -> (Just v , cont Empty)
{-# INLINABLE updateLookupWithKey #-}

findAndReplace :: CritBitKey k => t -> (v -> (Node k v -> CritBit k v) -> t)
               -> k -> CritBit k v -> t
findAndReplace notFound found k (CritBit root) = go root CritBit
  where
    go i@(Internal left right _ _) cont = 
      choose k i (go left  $ cont .! setLeft  i)
                 (go right $ cont .! setRight i)
    go (Leaf lk lv) cont
      | k == lk   = found lv cont
      | otherwise = notFound
    go Empty _ = notFound
{-# INLINE findAndReplace #-}

infixr 9 .!
(.!) :: (b -> c) -> (a -> b) -> a -> c
(.!) f g x = f $! g $! x

setLeft :: Node k v -> Node k v -> Node k v
setLeft i@(Internal{}) Empty = iright i
setLeft i@(Internal{}) node  = i { ileft = node }
setLeft _ _ = error "Data.CritBit.Core.setLeft: Non-internal node"
{-# INLINE setLeft #-}

setRight :: Node k v -> Node k v -> Node k v
setRight i@(Internal{}) Empty = ileft i
setRight i@(Internal{}) node  = i { iright = node }
setRight _ _ = error "Data.CritBit.Core.setRight: Non-internal node"
{-# INLINE setRight #-}

-- | Selects one of the values depending whether split specified
-- by `byte` and `bits` occurs before or after internal node
-- | move down the tree.
select :: Int -> BitMask -> Node k v -> a -> a -> a
select byte bits (Internal _ _ nbyte nbits) before after
    | byte < nbyte || byte == nbyte && bits < nbits = before
    | otherwise                                     = after
select _ _ _ _ _ = error "Data.CritBit.Core.select: unpossible!"
{-# INLINE select #-}

-- | Chooses one of the values depending on the direction we should
-- | move down the tree.
choose :: (CritBitKey k) => k -> Node k v -> a -> a -> a
choose k (Internal _ _ byte bits) left right
    | calcDirection bits (getByte k byte) == 0 = left
    | otherwise                                = right
choose _ _ _ _ = error "Data.CritBit.Core.choose: unpossible!"
{-# INLINE choose #-}

-- Given a critical bitmask and a byte, return 0 to move left, 1 to
-- move right.
calcDirection :: BitMask -> Word16 -> Int
calcDirection otherBits c = (1 + fromIntegral (otherBits .|. c)) `shiftR` 9
{-# INLINE calcDirection #-}

-- | Figure out the byte offset at which the key we are interested in
-- differs from the leaf we reached when we initially walked the tree.
--
-- We return some auxiliary stuff that we'll bang on to help us figure
-- out which direction to go in to insert a new node.
followPrefixes :: (CritBitKey k) =>
                  k             -- ^ The key from "outside" the tree.
               -> k             -- ^ Key from the leaf we reached.
               -> (Int, BitMask, Word16)
followPrefixes = followPrefixesFrom 0
{-# INLINE followPrefixes #-}

-- | Figure out the offset of the first different byte in two keys,
-- starting from specified position.
--
-- We return some auxiliary stuff that we'll bang on to help us figure
-- out which direction to go in to insert a new node.
followPrefixesFrom :: (CritBitKey k) =>
                      Int           -- ^ Positition to start from
                   -> k             -- ^ First key.
                   -> k             -- ^ Second key.
                   -> (Int, BitMask, Word16)
followPrefixesFrom !position !k !l = (n, maskLowerBits (b `xor` c), c)
  where
    n = followPrefixesByteFrom position k l
    b = getByte k n
    c = getByte l n

    maskLowerBits :: Word16 -> Word16
    maskLowerBits v = (n3 .&. (complement (n3 `shiftR` 1))) `xor` 0x1FF
      where
        n3 = n2 .|. (n2 `shiftR` 8)
        n2 = n1 .|. (n1 `shiftR` 4)
        n1 = n0 .|. (n0 `shiftR` 2)
        n0 = v  .|. (v  `shiftR` 1)
{-# INLINE followPrefixesFrom #-}

-- | Figure out the offset of the first different byte in two keys,
-- starting from specified position.
followPrefixesByteFrom :: (CritBitKey k) =>
                          Int           -- ^ Positition to start from
                       -> k             -- ^ First key.
                       -> k             -- ^ Second key.
                       -> Int
followPrefixesByteFrom !position !k !l = go position
  where
    go !n | b /= c || b == 0 || c == 0 = n
          | otherwise                  = go (n + 1)
      where b = getByte k n
            c = getByte l n
{-# INLINE followPrefixesByteFrom #-}

leftmost, rightmost :: a -> (k -> v -> a) -> Node k v -> a
leftmost  = extremity ileft
{-# INLINE leftmost #-}
rightmost = extremity iright
{-# INLINE rightmost #-}

-- | Generic function so we can easily implement 'leftmost' and 'rightmost'.
extremity :: (Node k v -> Node k v) -- ^ Either 'ileft' or 'iright'.
          -> a                      -- ^ 'Empty' continuation.
          -> (k -> v -> a)          -- ^ 'Leaf' continuation.
          -> Node k v
          -> a
extremity direct onEmpty onLeaf node = go node
  where
    go i@(Internal{}) = go $ direct i
    go (Leaf k v)     = onLeaf k v
    go _              = onEmpty
    {-# INLINE go #-}
{-# INLINE extremity #-}
