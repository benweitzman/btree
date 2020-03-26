{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Lib where

import Data.Coerce

someFunc :: IO ()
someFunc = putStrLn "someFunc"

-- | Nat is a reperesentation of the integers that's ammenable
-- to structural recursion
data Nat = Z | S Nat

type Two = 'S ('S 'Z)
type Three = 'S Two
type Four = 'S ('S Two)
type Six = 'S ('S Four)
type Eight = 'S ('S Six)

-- | SNat is a "singleton", which means that every type `SNat n`
-- has exatly 1 non-bottom inhabitant. This creates a 1-1 correspondence
-- between types and values which allows to essentially pattern match
-- on types.
data SNat n where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | Integer addition defined on our numbers
type family x :+ y where
  x :+ 'Z = x
  x :+ 'S n = 'S (x :+ n)

-- | `a :~: b` is a propisition that types `a` and `b` are equal.
-- There is only one inhabitant, `Refl` which provides a proof that
-- any type is equal to itself.
data (a :: k) :~: b where
  Refl :: a :~: a

-- x :: Int :~: Int
-- x = Refl

-- y :: Int :~: Bool
-- y = _


-- | Shuffle some types around to prove that `'S` associates through
-- `:+`
assoc :: forall x n . SNat n -> ('S x :+ n) :~: 'S (x :+ n)
assoc SZ = Refl
assoc (SS s) = case assoc @x s of
  Refl -> Refl

-- | Less than relation on integers. There are many ways to represent this concept
-- we've chosen one here that is useful to our domain. It will let us keep track
-- easily of how much `x` is less than `y`
data (x :: Nat) :<=: (y :: Nat) where
  LTPrf :: SNat z -> (x :+ z) :~: y-> x :<=: y

-- | Try and increase the left hand side of our relation.
-- In the case that x = y, we can't increase x and maintain the
-- relation, so we return a Nothing value instead.
inc :: forall x y . x :<=: y -> Maybe ('S x :<=: y)
inc (LTPrf SZ Refl) = Nothing
inc (LTPrf (SS s) Refl) = Just $ LTPrf s (assoc @x s)

-- 3 <= 5 (z = 2, 3 + 2 == 5)
-- 4 <= 5 (z = (2 - 1), 4 + 1 == 5)

-- | Maintain a less than relation when we add one to the
-- left hand side and 2 to the right hand sand
incRightTwice :: forall x y . x :<=: y -> 'S x :<=: 'S ('S y)
incRightTwice (LTPrf SZ Refl) = LTPrf (SS SZ) Refl
incRightTwice (LTPrf (SS n) Refl) = LTPrf (SS (SS n)) $ case assoc @x n of
  Refl -> Refl

-- | Maintain a less than relation when we decrement the left hand side
dec :: forall x y . 'S x :<=: y -> x :<=: y
dec (LTPrf SZ Refl) = LTPrf (SS SZ) Refl
dec (LTPrf (SS n) Refl) = LTPrf (SS (SS n)) $ case assoc @x n of
  Refl -> Refl

-- | BProp makes the claim of the b-tree property that all nodes except for the
-- root must be _at least_ half full
data BProp (size :: Nat) (order :: Nat) where
  BZ :: BProp size 'Z
  BS :: BProp s o -> BProp ('S s) ('S ('S o))

-- | Increase the number of values in a node, which should maintain the
-- b-tree property
incBProp :: BProp size order -> BProp ('S size) order
incBProp BZ = BZ
incBProp (BS bp) = BS $ incBProp bp

-- | Nodes in our b-tree are length-indexed linked lists with subtrees interleaved
-- with values.
data Node (size :: Nat) (order :: Nat) a where
  Child :: BTree 'NotRoot order a -> Node 'Z order a
  Key :: BTree 'NotRoot order a -> a -> Node k order a -> Node ('S k) order a

-- | Tag for keeping track of whether a tree is a subtree or root
data IsRoot = IsRoot | NotRoot


-- | BTree representation. Each b-tree is indexed by two parameters:
-- * whether or not it is a root
-- * the order of the tree
--
-- A B-tree is formed from nodes and leafs with the following properties:
-- * Leafs carry no information
-- * Non-root nodes contain between [order/2] and order values
-- * All nodes contain 1 more subtrees than values
-- * The root node can have less than [order/2] values, but still can't have more than order
--
-- These properties ensure that the tree is reasonably balanced and that search/insert/etc operations
-- stay O(logn)
--
-- When we construct b-trees, we have to provide "proofs" of these properties. This ensures that as we
-- modify the tree we are maintaining the proper structure.
data BTree (root :: IsRoot) (order :: Nat) a where
  Leaf :: BTree 'NotRoot order a
  Root :: size :<=: order -> Node size order a -> BTree 'IsRoot order a
  Internal :: BProp size order -> size :<=: order -> Node size order a -> BTree 'NotRoot order a

-- | The `Order` typeclass gives us a few functions that are parameterized over the
-- order of a tree. Combined with the singletons, this helps us do something like
-- pattern matching on type level orders.
class Order o where
  startNode :: 'S 'Z :<=: o

  split :: Overflow k ('S o) o a -> OSplit k o a

-- | Split a node that is too big to fit in the tree in to 2 smaller ones
splitNode :: Order o => Node ('S o) o a -> Split o a
splitNode = toSplit . split . overflow

data Split order a = Split
  { left :: BTree 'NotRoot order a
  , median :: a
  , right :: BTree 'NotRoot order a
  }

empty :: Order order => BTree 'IsRoot order a
empty = Root (dec startNode) (Child Leaf)

search :: Ord a => a -> BTree r order a -> Maybe a
search _ Leaf = Nothing
search key (Root _ node) = searchNode key node
search key (Internal _ _ node) = searchNode key node

searchNode :: Ord a => a -> Node size order a -> Maybe a
searchNode key (Child tree) = search key tree
searchNode key (Key left key' rest) = case compare key key' of
  LT -> search key left
  EQ -> Just key
  GT -> searchNode key rest


-- | Insert describes the possible results of inserting into a b-tree.
-- For a root tree, the result is always a nother root tree.
-- For subtrees, they can potentially become overflowed and need to split
type family Insert r order a where
  Insert 'IsRoot order a = BTree 'IsRoot order a
  Insert 'NotRoot order a = Either (BTree 'NotRoot order a) (Split order a)

-- | Insert a value into a b-tree, possibly splitting the tree if it becomes full
insert :: (Ord a, Order order) => a -> BTree r order a -> Insert r order a
-- leafs never contain data, so if we try to insert a value into one, we consider it
-- full and must split.
insert v Leaf = Right $ Split -- note how we use `Right` here. Pattern matching Leaf disambiguates the
  { left = Leaf               -- return type to `Insert 'NotRoot order a`, which unambigulously refers
  , right = Leaf              -- the either case .
  , median = v
  }
-- insert into a root node can potentially overflow the root. If this happens,
-- we can't return a split node (because we're the root). Instead, we have to split and
-- create a new root node.
insert v (Root full (node :: Node size order a)) = case insertNode v node of
  NodeNoChange node' -> Root full node'
  NodeChange node' -> case full of
    LTPrf SZ Refl -> case splitNode node' of
      Split{left,median,right} -> Root startNode $ Key left median $ Child right
    LTPrf (SS n) Refl -> Root (LTPrf n $ assoc @size n) node'
-- insert into an internal node, and potentially split if the node then becomes overflowed
insert v (Internal bProp full (node :: Node size order a)) = case insertNode v node of
  NodeNoChange node' -> Left $ Internal bProp full node'
  NodeChange node' -> case full of
    LTPrf SZ Refl -> Right $ splitNode node'
    LTPrf (SS n) Refl -> Left $ Internal (incBProp bProp) (LTPrf n $ assoc @size n) node'

-- | The possible results of inserting a value into a node. If the value
-- belongs in the node, then it will increase the size. Otherwise it will
-- make its way into a subtree and not change the size of this node.
data NodeInserted sizeIn order a where
  NodeChange :: Node ('S sizeIn) order a -> NodeInserted sizeIn order a
  NodeNoChange :: Node sizeIn order a -> NodeInserted sizeIn order a

mapNode
  :: (forall s . Node s order a -> Node ('S s) order a)
  -> NodeInserted sizeIn order a
  -> NodeInserted ('S sizeIn) order a
mapNode f (NodeChange n) = NodeChange $ f n
mapNode f (NodeNoChange n) = NodeNoChange $ f n

-- | Inserting into a node is like iterating through a linked list to find
-- the proper insertion point, which will always be a subtree.
--
-- If the subtree splits after having a new value inserted, then
-- incorporate that value into this node, increasing its size by 1
insertNode :: (Ord a, Order order) => a -> Node size order a -> NodeInserted size order a
insertNode val (Child tree) = case insert val tree of
  Left tree' -> NodeNoChange $ Child tree'
  Right Split{left,median,right} -> NodeChange . Key left median $ Child right
insertNode val self@(Key tree val' rest) = case compare val val' of
  LT -> case insert val tree of
    Left tree' -> NodeNoChange $ Key tree' val' rest
    Right Split{left,median,right} -> NodeChange $ Key left median (Key right val' rest)
  EQ -> NodeNoChange self
  GT -> mapNode (Key tree val') $ insertNode val rest

treeShow :: Show a => BTree r order a -> [String]
treeShow Leaf = ["."]
treeShow (Root _ node) = nodeShow node
treeShow (Internal _ _ node) = nodeShow node

nodeShow :: Show a => Node size order a -> [String]
nodeShow (Child tree) = zipWith (++) ("-->" : repeat "   ") (treeShow tree)
nodeShow (Key tree val rest) = nodeShow (Child tree) ++ [show val] ++ nodeShow rest

instance Show a => Show (BTree r order a) where
  show tree = unlines $ treeShow tree


-- Everything below here is helper data types + functions for dealing with splitting b-tree nodes
-- recursively over their order. Splitting only works for even orders right now. This makes recursion
-- much simpler:
--
-- splitting an overflowed node of order 2 (base case)
--
--   [1, 2, 3] ->    2
--                 /   \
--               [1]   [3]
--
-- splitting an overflowed node of order n + 2:
--
--       [1,2,..,n, n + 2, n + 3]
--
--       break into [1, 2] + [3, 4 .. n, n + 2, n + 3], which is like an overflowed node of order n
--
--       split [3, 4 .. n, n + 2, n + 3] ->  m
--                                         /   \
--                                    [l.., l']  r
--
--       We don't what values end up in l and r, but we know they both have size n / 2
--
--      work [1,2] in the tree:
--
--                l '
--          /          \
--  [1, 2, ...l]     (m : r)
--
--
-- Note: Doing this recursively is slow and silly :D


data Overflow (order :: Nat) (size :: Nat) (window :: Nat) a where
  OChild :: BTree 'NotRoot order a -> Overflow order 'Z window a
  OKey :: BTree 'NotRoot order a -> a -> Overflow order k window a -> Overflow order ('S k) window a

shrink :: Overflow order ('S k) ('S ('S k)) a -> Overflow order ('S k) k a
shrink = coerce

overflow :: Node k o a -> Overflow o k o a
overflow (Child x) = OChild x
overflow (Key l v r) = OKey l v $ overflow r

unoverflow :: Overflow o k o a -> Node k o a
unoverflow (OChild x) = Child x
unoverflow (OKey l v r) = Key l v $ unoverflow r

unsnoc :: Overflow o ('S k) n a -> (Overflow o k n a, a, BTree 'NotRoot o a)
unsnoc (OKey l v (OChild r)) = (OChild l, v, r)
unsnoc (OKey l v r@OKey{}) = case unsnoc r of
  (o', x, z) -> (OKey l v o', x, z)


toSplit :: OSplit o o a -> Split o a
toSplit OSplit
  { oLeft = OPre lProp lSize lTree
  , oMedian
  , oRight = OPre rProp rSize rTree
  } = Split
      { left = Internal lProp lSize (unoverflow lTree)
      , median = oMedian
      , right = Internal rProp rSize (unoverflow rTree)
      }

instance {-# OVERLAPPING #-} Order Two where
  startNode = LTPrf (SS SZ) Refl

  split (OKey a x (OKey b y (OKey c z (OChild d)))) = OSplit
    { oLeft = OPre (BS BZ) startNode $ OKey a x (OChild b)
    , oMedian = y
    , oRight = OPre (BS BZ) startNode $ OKey c z (OChild d)
    }


instance Order n => Order ('S ('S n)) where
  startNode = case startNode @n of
    LTPrf x Refl -> LTPrf (SS (SS x)) Refl

  split (OKey a x (OKey b y rest)) = case split @n $ shrink rest of
      OSplit
        { oLeft = OPre lProp lSize lTree
        ,oMedian
        ,oRight = OPre rProp rSize rTree
        } -> case unsnoc (OKey a x (OKey b y lTree)) of
               (left', median', right') -> OSplit
                 { oLeft = OPre (BS lProp) (incRightTwice lSize) (coerce left')
                 , oMedian = median'
                 , oRight = OPre (BS rProp) (incRightTwice rSize) (coerce $ OKey right' oMedian rTree)
                 }

data OPre order window a where
  OPre :: BProp size window -> size :<=: window -> Overflow order size window a -> OPre order window a

data OSplit order window a = OSplit
    { oLeft :: OPre order window a
    , oMedian :: a
    , oRight :: OPre order window a
    }
