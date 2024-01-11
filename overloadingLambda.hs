-- Following this great blog post:
-- https://acatalepsie.fr/posts/overloading-lambda
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -W #-}

module OverloadingLambda where

import Control.Arrow
import Control.Category
import Prelude hiding (fst, id, snd, (.), (>>))

data Flow a b where
    Id :: Flow a a
    Seq :: Flow a b -> Flow b c -> Flow a c
    Par :: Flow a b -> Flow c d -> Flow (a, c) (b, d)
    Dup :: Flow a (a, a)
    Void :: Flow a ()
    Fst :: Flow (a, b) a
    Snd :: Flow (a, b) b
    Embed :: (a -> b) -> Flow a b

instance Category Flow where
    id :: Flow a a
    id = Id
    (.) :: Flow b c -> Flow a b -> Flow a c
    (.) = flip Seq

instance Arrow Flow where
    arr :: (b -> c) -> Flow b c
    arr = Embed
    first :: Flow b c -> Flow (b, d) (c, d)
    first = flip Par Id
    second :: Flow b c -> Flow (d, b) (d, c)
    second = Par Id
    (***) :: Flow b c -> Flow b' c' -> Flow (b, b') (c, c')
    (***) = Par
    (&&&) :: Flow b c -> Flow b c' -> Flow b (c, c')
    (&&&) f1 f2 = Seq Dup (Par f1 f2)

newtype Port a b = P {unPort :: Flow a b}

encode :: Flow a b -> Port r a -> Port r b
encode f (P g) = P (f . g)

decode :: (forall r. Port r a -> Port r b) -> Flow a b
decode f = unPort (f (P id))

pair :: Port r a -> Port r b -> Port r (a, b)
pair (P f) (P g) = P (f &&& g)

unit :: Port r ()
unit = P Void

flow = decode

fst :: Port r (a, b) -> Port r a
fst = encode Fst

snd :: Port r (a, b) -> Port r b
snd = encode Snd

split :: Port r (a, b) -> (Port r a, Port r b)
split p = (fst p, snd p)

void :: Port r a -> Port r ()
void = encode Void

box :: (a -> b) -> Port r a -> Port r b
box f = encode (Embed f)

(>>) :: Port r a -> Port r b -> Port r b
x >> y = snd (pair x y)

box1 :: Port r String -> Port r (Int, Int)
box1 = box (\s -> (read s, read s))

box2 :: Port r String -> Port r Bool
box2 = box (== [])

box3 :: Port r Int -> Port r ()
box3 = void

box4 :: Port r Int -> Port r ()
box4 = void

diag :: Flow (String, String) Bool
diag =
    flow
        ( \p ->
            let (x, y) = split p
                (a, b) = split (box1 x)
             in (box3 a >> box4 b) >> box2 y
        )

pattern Tup x y <- (split -> (x, y))
    where
        -- below is unnecessary
        Tup x y = pair x y

diag' :: Flow (String, String) Bool
diag' = flow $ \(Tup x y) -> OverloadingLambda.do
    let Tup a b = box1 x
    box3 a
    box4 b
    box2 y
